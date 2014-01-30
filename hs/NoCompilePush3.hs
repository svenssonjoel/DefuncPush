

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
-- Push Language
---------------------------------------------------------------------------
data PushT b  where
  Generate :: Length -> (Ix -> b) ->PushT b
  Use :: Length -> V.Vector b -> PushT b 

  Map :: (a -> b) -> PushT a -> PushT b

  IMap :: (Ix -> a -> b) -> PushT a -> PushT b

  Append :: Ix -> PushT b -> PushT b -> PushT b

  Interleave :: PushT b -> PushT b -> PushT b  

  -- Permutations
  Reverse :: PushT b -> PushT b
  Rotate  :: Length -> PushT b -> PushT b 
  
-- now PushT can be used as the array type (without any Push Wrapper) 
pushLength :: PushT b -> Length
pushLength (Generate l _) = l
pushLength (Use l _) = l
pushLength (Map _ p )  = pushLength p
pushLength (IMap _ p)  = pushLength p
pushLength (Append _ p1 p2) = pushLength p1 + pushLength p2
pushLength (Interleave p1 p2) = 2 * (min (pushLength p1) (pushLength p2))
pushLength (Reverse p) = pushLength p
pushLength (Rotate _ p) = pushLength p 

len = pushLength 


---------------------------------------------------------------------------
-- Apply
---------------------------------------------------------------------------

apply :: PrimMonad m => PushT a -> (Ix -> a -> m ()) -> m ()
apply (Generate n ixf) =
  \k -> forM_ [0..(n-1)] $ \i ->
          k i (ixf i)
                           
apply (Use l mem) =
  \k -> forM_ [0..(l-1)] $ \i ->
          k i (mem V.! i)  

apply (Map f p) =
  \k -> apply p (\i a -> k i (f a))


apply (IMap f p) =
  \k -> apply p (\i a -> k i (f i a))

apply (Append l p1 p2) =
  \k -> apply p1 k >>
        apply p2 (\i a -> k (l + i) a)
        
apply (Interleave p1 p2) =
  \k -> apply p1 (\i a -> k (2*i) a) >> 
        apply p2 (\i a -> k (2*i+1) a) 
  
apply (Reverse p) =
  \k -> apply p (\i a -> k ((len p) - 1 - i) a)
        
apply (Rotate n p) =
  \k -> apply p (\i a -> k ((i + n) `mod` (len p)) a)

---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

(<:) :: PrimMonad m => PushT a -> (Ix -> a -> m ()) -> m () 
p <: k = apply p k

use :: Length -> V.Vector a -> PushT a
use mem l = Use mem l

map :: (a -> b) -> PushT a -> PushT b
map f p= Map f p

imap :: (Ix -> a -> b) -> PushT a -> PushT b
imap f p = IMap f p

(++) :: PushT a -> PushT a  -> PushT a
p1 ++ p2 = Append (len p1) p1 p2  

interleave :: PushT a -> PushT a -> PushT a
interleave p1 p2 = Interleave p1 p2 

reverse :: PushT a -> PushT a
reverse p = Reverse p 

rotate :: Length -> PushT a -> PushT a
rotate n p = Rotate n p 



---------------------------------------------------------------------------
-- Conversion Pull Push (Clean this mess up)
---------------------------------------------------------------------------

push (Pull ixf n) =
  Generate n ixf


---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: PrimMonad m => PushT a -> m (V.Vector a)
freeze p =
  do
     arr <- M.new (len p) 
     apply p (\i a -> M.write arr i a)
     V.freeze arr

toVector :: PrimMonad m => PushT a -> m (V.Vector a)
toVector = freeze 

---------------------------------------------------------------------------
-- Experiments Push a -> Pull a
---------------------------------------------------------------------------

index :: PushT a -> Ix -> a
index (Map f p) ix = f (index p ix)
index (Use l v) ix = v V.! ix  
index (Generate n ixf) ix = ixf ix
index (IMap f p) ix = f ix (index p ix)
index (Append l p1 p2) ix =
  if (ix < l)
  then index p1 ix
  else index p2 (ix - l)
index (Interleave p1 p2) ix =
  if (ix `mod` 2 == 0)
  then index p1 (ix `div` 2)
  else index p2 (ix `div` 2)

index (Reverse p) ix = index p (len p - 1 - ix)
index (Rotate dist p) ix = index p ((ix - dist) `mod` (len p)) 

---------------------------------------------------------------------------
-- Push to Pull
---------------------------------------------------------------------------

convert :: PushT a -> Pull a
convert p = Pull (\ix -> index p ix) (len p) 

---------------------------------------------------------------------------
-- Functions from Pull array library
---------------------------------------------------------------------------
-- zip, take, drop, head

zipP :: PushT a -> PushT b -> PushT (a,b)
zipP p1 p2 = push $ zipPull (convert p1) (convert p2) 
-- converting pull to push is cheap.
-- Converting a push to pull is potentially costly...
-- But the convert function kind-of-cheats in the iterate case. 

head :: PushT a -> a
head p = index p 0 

take :: Length -> PushT a -> PushT a
take n p = push (takePull n (convert p))

drop :: Length -> PushT a -> PushT a
drop n p = push (dropPull n (convert p))

---------------------------------------------------------------------------
-- Simple programs
---------------------------------------------------------------------------
input1 = Pull id 16

simple1 = map (+1) . push 

runSimple1 = toVector (simple1 input1 :: PushT Int)
-- Above: uses pull array for inputs 

-- Example without pull arrays entirely
myVec = V.fromList [0..9] 

usePrg :: (Enum b, Num b) => PushT b
usePrg = rotate 3 $ reverse $ map (+1) (use 10 myVec )

runUse :: IO (V.Vector Int)
runUse = toVector (usePrg :: PushT Int) 


-- zipP test
prg :: (Enum a, Enum b, Num a, Num b) => PushT (a, b)
prg = zipP (use 10 myVec) (use 10 myVec)

runPrg :: IO (V.Vector (Int, Int))
runPrg = toVector (prg :: PushT (Int,Int))
-- Running this requires a Use case in index
-- which requires index to be monadic
-- which requires there to be a function push :: Pull (m a) -> Push m a
--   for the cheat version of zipP to work 


-- fusion  :: (Num a, Num ix, ForMonad ctxt ix m)
--          => Pull ix a -> PushT ix a
-- fusion = map (+1) . map (*2) . push 

-- 
-- test11 :: (Num a, Num ix,
--            ctxt a, MemMonad ctxt mem ix a m,
--            ForMonad ctxt ix m)
--           => Pull ix a -> PushT ix a
-- test11 = map (+1) . force . map (+1) . push  

-- runTest11' = do { s <- runTest11; (getElems s)}


-- usePrg :: (Num a, Num ix, ctxt a, MemMonad ctxt mem ix a m, ForMonad ctxt ix m)
--           => mem ix a -> PushT ix a 
-- 

saxpy :: Float -> PushT Float -> PushT Float -> PushT Float
saxpy a x y = imap (\i xi -> (a * xi + index y i)) x 


runSaxpy :: IO (V.Vector Float)
runSaxpy = toVector $ saxpy 1.5 (use 10 x) (use 10 y)  
   where
     x = V.fromList [0..9] 
     y = V.fromList (replicate 10 1)
