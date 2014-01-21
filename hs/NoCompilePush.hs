

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-} 
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE NoMonomorphismRestriction #-} 


module NoCompilePush where


import Control.Monad
import Control.Monad.ST

import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Primitive
import Data.RefMonad


import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M 

import Prelude hiding (reverse,scanl,map,read)
import qualified Prelude as P 

import GHC.Prim (Constraint) 

---------------------------------------------------------------------------
-- Some basics
---------------------------------------------------------------------------

type Length = Int 
type Ix     = Int

---------------------------------------------------------------------------
-- Pull array
---------------------------------------------------------------------------

data Pull a = Pull (Ix -> a) Length

zipPull :: Pull a -> Pull b -> Pull (a,b)
zipPull (Pull p1 n1) (Pull p2 n2) = Pull (\i -> (p1 i, p2 i)) (min n1 n2) 

takePull :: Length -> Pull a -> Pull a
takePull n (Pull ixf l) = Pull ixf n

dropPull :: Length -> Pull a -> Pull a
dropPull n (Pull ixf l) = Pull (\i -> ixf (i+n)) (l - n)

---------------------------------------------------------------------------
-- Convert to Pull array
--------------------------------------------------------------------------- 
class PullFrom c where
  pullFrom :: c a -> Pull a

instance PullFrom Pull where
  pullFrom = id 


---------------------------------------------------------------------------
-- Write Function language
---------------------------------------------------------------------------
data Write m a where
  MapW :: Write m b -> (a -> b) -> Write m a
  ApplyW :: (Ix -> a -> m ()) -> Write m a
  VectorW :: PrimMonad m => M.MVector (PrimState m) a -> Write m a

  IMapW :: Write m b -> (a -> Ix -> b) -> Write m a

  IxMapW :: Write m a -> (Ix -> Ix) -> Write m a

  AppendW :: Write m a -> Ix -> Write m a

  -- replace by arith ? 
  EvensW :: Write m a -> Write m a
  OddsW  :: Write m a -> Write m a

  ReverseW :: Length -> Write m a -> Write m a
  RotateW  :: Length -> Length -> Write m a -> Write m a 


---------------------------------------------------------------------------
-- Apply Write 
---------------------------------------------------------------------------
  
applyW :: Write m a -> (Ix -> a -> m ())
applyW (MapW k f) =  \i a -> applyW k i (f a)
applyW (ApplyW k) = k
applyW (VectorW v) = \i a -> M.write v i a

applyW (IMapW k f) = \i a -> applyW k i (f a i)
applyW (IxMapW k f) = \i a -> applyW k (f i) a

applyW (AppendW k l) = \i a -> applyW k (l + i) a
applyW (EvensW k) = \i a -> applyW k (2*i) a
applyW (OddsW k)  = \i a -> applyW k (2*i+1) a 

applyW (ReverseW l k) = \i a -> applyW k (l - 1 - i) a
applyW (RotateW l n k) = \i a -> applyW k ((i + n) `mod` l) a 

---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------
data PushT m b  where
  Map  :: PushT m a -> (a -> b) -> PushT m b

  -- array creation 
  Generate :: Monad m => (Ix -> b) -> Length -> PushT m b
  GenerateM :: Monad m => (Ix -> m b) -> Length -> PushT m b
  
  Use :: (PrimMonad m) => V.Vector b -> Length -> PushT m b 

  Force :: PrimMonad m => PushT m b -> Length -> PushT m b 

--  IxMap :: PushT m b -> (Ix -> Ix) -> PushT m b
  IMap :: PushT m a -> (a -> Ix -> b) -> PushT m b
  Iterate :: RefMonad m r => (b -> b) -> b -> Length -> PushT m b 

  Append :: Monad m => Ix -> PushT m b -> PushT m b -> PushT m b

  Interleave :: Monad m => PushT m b -> PushT m b -> PushT m b  

  -- Permutations
  Reverse :: PushT m b -> PushT m b
  Rotate  :: Length -> PushT m b -> PushT m b 
  
-- now PushT can be used as the array type (without any Push Wrapper) 
pushLength :: PushT m b -> Length
pushLength (Generate _ l) = l
pushLength (GenerateM _ l) = l
pushLength (Use _ l) = l
pushLength (Force _ l) = l
pushLength (Iterate _ _ l) = l
pushLength (Map p _ )  = pushLength p
--pushLength (IxMap p _) = pushLength p
pushLength (IMap p _)  = pushLength p
pushLength (Append _ p1 p2) = pushLength p1 + pushLength p2
pushLength (Interleave p1 p2) = 2 * (min (pushLength p1) (pushLength p2))

pushLength (Reverse p) = pushLength p
pushLength (Rotate _ p) = pushLength p 

len = pushLength 


---------------------------------------------------------------------------
-- Apply
---------------------------------------------------------------------------
  
apply :: PushT m b -> (Write m b -> m ())
apply (Map p f) = \k -> apply p (MapW k f)
apply (Generate ixf n) = \k -> forM_ [0..(fromIntegral n-1)] $ \i ->
                           applyW k i (ixf i)
apply (GenerateM ixf n) = \k -> forM_ [0..(fromIntegral n-1)] $ \i ->
                           do a <- ixf i       
                              applyW k i a

apply (Use mem l) = \k -> forM_ [0..(fromIntegral l-1)] $ \i ->
                               applyW k i (mem V.! i)  


apply (IMap p f) = \k -> apply p (IMapW k f)

--apply (IxMap p f) = \k -> apply p (IxMapW k f) 

apply (Append l p1 p2) = \k -> apply p1 k >>
                               apply p2 (AppendW k l)

apply (Interleave p1 p2) = \k -> apply p1 (EvensW k) >> 
                                 apply p2 (OddsW k) 
  


apply (Iterate f a n) = \k ->
  do
    sum <- newRef a 
    forM_ [0..(fromIntegral n-1)] $ \i ->
      do
        val <- readRef sum
        applyW k i val 
        writeRef sum (f val) 


apply (Force p l) =
  \k -> do arr <- M.new l 
           apply p  (VectorW arr)
           imm <- V.freeze arr
           forM_ [0..(fromIntegral l-1)] $ \ix ->
                applyW k ix (imm V.! ix) 
        

apply (Reverse p) =
  \k -> apply p (ReverseW (len p) k)
apply (Rotate n p) =
  \k -> apply p (RotateW (len p) n k) 

---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

(<:) :: PushT m a -> (Ix -> a -> m ()) -> m () 
p <: k = apply p (ApplyW k)

use :: PrimMonad m => V.Vector a -> Length -> PushT m a
use mem l = Use mem l
-- undefunctionalized
-- use :: PrimMonad m => V.Vector a -> Length -> Push m a
-- use mem l = Push p l
--   where
--     p k = forM_ [0..l-1] $ \ix ->
--             k ix (mem V.! ix) 


map :: (a -> b) -> PushT m a -> PushT m b
map f p= Map p f

imap :: (a -> Ix -> b) -> PushT m a -> PushT m b
imap f p = IMap p f

--ixmap :: (Ix -> Ix) -> PushT m a -> PushT m a
--ixmap f p = IxMap p f

(++) :: Monad m => PushT m a -> PushT m a  -> PushT m a
p1 ++ p2 = Append (len p1) p1 p2  

iterate :: RefMonad m r => Length -> (a -> a) -> a -> PushT m a
iterate n f a = Iterate f a n

interleave :: Monad m => PushT m a -> PushT m a -> PushT m a
interleave p1 p2 = Interleave p1 p2 

reverse :: PushT m a -> PushT m a
reverse p = Reverse p 

rotate :: Length -> PushT m a -> PushT m a
rotate n p = Rotate n p 



---------------------------------------------------------------------------
-- Conversion Pull Push (Clean this mess up)
---------------------------------------------------------------------------

push (Pull ixf n) =
  Generate ixf n

class ToPush m arr where
  toPush ::  arr a -> PushT m a

instance Monad m => ToPush m (PushT m) where
  toPush = id

pushM :: Monad m => Pull (m a) -> PushT m a 
pushM (Pull ixf n) = GenerateM ixf n 


-- Not so fun... 
pushM2 :: Monad m => Pull (m a, m b) -> PushT m (a,b) 
pushM2 (Pull ixf n) = GenerateM (c . ixf) n
  where
    c (a,b) = do a' <- a
                 b' <- b
                 return (a', b') 


---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: PrimMonad m => PushT m a -> m (V.Vector a)
freeze p =
  do
     arr <- M.new (len p) 
     apply p (VectorW arr)
     V.freeze arr

toVector :: PrimMonad m => PushT m a -> m (V.Vector a)
toVector = freeze 

---------------------------------------------------------------------------
-- A defunctionalisable "freeze", called force. 
---------------------------------------------------------------------------
     
force :: PrimMonad m => PushT m a -> PushT m a
force p = Force p (len p) 

---------------------------------------------------------------------------
-- Experiments Push a -> Pull a
---------------------------------------------------------------------------

index_ :: PushT m a -> Ix -> a
index_ (Map p f) ix = f (index_ p ix)
index_ (Generate ixf n) ix = ixf ix
index_ (IMap p f) ix = f (index_ p ix) ix
index_ (Iterate f a l) ix = P.iterate f a P.!! ix 
--index_ (Iterate f a l) ix =
--  do sum <- newRef a
--     forM_ [0..ix-1] $ \i -> 
--       do val <- readRef sum
--          writeRef sum (f val)
--     readRef sum
index_ (Append l p1 p2) ix =
  if (ix < l)
  then index_ p1 ix
  else index_ p2 (ix - l)
index_ (Interleave p1 p2) ix =
  if (ix `mod` 2 == 0)
  then index_ p1 (ix `div` 2)
  else index_ p2 (ix `div` 2)

index_ (Reverse p) ix = index_ p (len p - 1 - ix)
index_ (Rotate dist p) ix = index_ p ((ix - dist) `mod` (len p)) 


indexM_ :: Monad m => PushT m a -> Ix -> m a
indexM_ (Map p f) ix = liftM f (indexM_ p ix)
indexM_ (Use v l) ix = return $ v V.! ix 
indexM_ (Generate ixf n) ix = return $ ixf ix
indexM_ (GenerateM ixf n) ix = ixf ix 
indexM_ (IMap p f) ix = do a <- indexM_ p ix
                           return $ f a ix
indexM_ (Iterate f a l) ix = return $ P.iterate f a P.!! ix 
indexM_ (Append l p1 p2) ix =
  if (ix < l)
  then indexM_ p1 ix
  else indexM_ p2 (ix - l)
indexM_ (Interleave p1 p2) ix =
  if (ix `mod` 2 == 0)
  then indexM_ p1 (ix `div` 2)
  else indexM_ p2 (ix `div` 2) 
indexM_ (Reverse p) ix = indexM_ p (len p - 1 - ix)
indexM_ (Rotate dist p) ix = indexM_ p ((ix - dist) `mod` (len p)) 

--index_ (Iterate f a l) ix =
--  do sum <- newRef a
--     forM_ [0..ix-1] $ \i -> 
--       do val <- readRef sum
--          writeRef sum (f val)
--     readRef sum


---------------------------------------------------------------------------
-- Push to Pull
---------------------------------------------------------------------------

convert :: PushT m a -> Pull a
convert p = Pull (\ix -> index_ p ix) (len p) 

-- convertM should work with use (atleast the plan) 
convertM :: Monad m =>  PushT m a -> Pull (m a)
convertM p = Pull (\ix -> indexM_ p ix) (len p) 
---------------------------------------------------------------------------
-- Functions from Pull array library
---------------------------------------------------------------------------
-- zip, take, drop, head

zipP :: Monad m => PushT m a -> PushT m b -> PushT m (a,b)
--zipP = undefined -- (and tricky)
-- Cheat sol.
zipP p1 p2 = push $ zipPull (convert p1) (convert p2) 
-- converting pull to push is cheap.
-- Converting a push to pull is potentially costly...
-- But the convert function kind-of-cheats in the iterate case. 

zipPM :: Monad m => PushT m a -> PushT m b -> PushT m (a,b)
zipPM p1 p2 = pushM2 $ zipPull (convertM p1) (convertM p2) 


head :: PushT m a -> a
head p = index_ p 0 

take :: Monad m => Length -> PushT m a -> PushT m a
take n p = push (takePull n (convert p))

drop :: Monad m => Length -> PushT m a -> PushT m a
drop n p = push (dropPull n (convert p))

---------------------------------------------------------------------------
-- Simple programs
---------------------------------------------------------------------------
input1 = Pull id 16

simple1 = map (+1) . push 

runSimple1 = toVector (simple1 input1 :: PushT IO Int)
-- Above: uses pull array for inputs 



-- Example without pull arrays entirely
myVec = V.fromList [0..9] 

usePrg :: (Enum b, Num b, PrimMonad m) => PushT m b
usePrg = rotate 3 $ reverse $ map (+1) (use myVec 10 )

runUse :: IO (V.Vector Int)
runUse = toVector (usePrg :: PushT IO Int) 


-- zipP test
prg :: (Enum a, Enum b, Num a, Num b, PrimMonad m) => PushT m (a, b)
prg = zipPM (use myVec 10) (use myVec 10)

runPrg :: IO (V.Vector (Int, Int))
runPrg = toVector (prg :: PushT IO (Int,Int))
-- Running this requires a Use case in index_
-- which requires index_ to be monadic
-- which requires there to be a function push :: Pull (m a) -> Push m a
--   for the cheat version of zipP to work 


-- fusion  :: (Num a, Num ix, ForMonad ctxt ix m)
--          => Pull ix a -> PushT m ix a
-- fusion = map (+1) . map (*2) . push 

-- 
-- test11 :: (Num a, Num ix,
--            ctxt a, MemMonad ctxt mem ix a m,
--            ForMonad ctxt ix m)
--           => Pull ix a -> PushT m ix a
-- test11 = map (+1) . force . map (+1) . push  

-- runTest11' = do { s <- runTest11; (getElems s)}


-- usePrg :: (Num a, Num ix, ctxt a, MemMonad ctxt mem ix a m, ForMonad ctxt ix m)
--           => mem ix a -> PushT m ix a 
-- 
