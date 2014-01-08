

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

  IxMapW :: Write m a -> (Ix -> Ix) -> Write m  a

  AppendW :: Write m a -> Ix -> Write m  a


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

---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------
data PushT m b  where
  Map  :: PushT m a -> (a -> b) -> PushT m b

  -- array creation 
  Generate :: Monad m => (Ix -> b) -> Length -> PushT m b
  Use :: (PrimMonad m) => V.Vector b -> Length -> PushT m b 

  Force :: PrimMonad m => PushT m b -> Length -> PushT m b 

  IxMap :: PushT m b -> (Ix -> Ix) -> PushT m b
  IMap :: PushT m a -> (a -> Ix -> b) -> PushT m b
  Iterate :: RefMonad m r => (b -> b) -> b -> Length -> PushT m b 

  Append :: (Monad m) => Ix -> PushT m b -> PushT m b -> PushT m b

-- now PushT can be used as the array type (without any Push Wrapper) 
pushLength :: PushT m b -> Length
pushLength (Generate _ l) = l
pushLength (Use _ l) = l
pushLength (Force _ l) = l
pushLength (Iterate _ _ l) = l
pushLength (Map p _ )  = pushLength p
pushLength (IxMap p _) = pushLength p
pushLength (IMap p _)  = pushLength p
pushLength (Append _ p1 p2) = pushLength p1 + pushLength p2

len = pushLength 


---------------------------------------------------------------------------
-- Apply
---------------------------------------------------------------------------
  
apply :: PushT m b -> (Write m b -> m ())
apply (Map p f) = \k -> apply p (MapW k f)
apply (Generate ixf n) = \k -> forM_ [0..(fromIntegral n-1)] $ \i ->
                           applyW k i (ixf i)

apply (Use mem l) = \k -> forM_ [0..(fromIntegral l-1)] $ \i ->
                            --do a <- readArray mem i
                               applyW k i (mem V.! i) -- a 


apply (IMap p f) = \k -> apply p (IMapW k f)

apply (IxMap p f) = \k -> apply p (IxMapW k f) 

apply (Append l p1 p2) = \k -> apply p1 k >>
                               apply p2 (AppendW k l)


apply (Iterate f a n) = \k ->
  do
    sum <- newRef a 
    forM_ [0..(fromIntegral n-1)] $ \i ->
      do
        val <- readRef sum
        applyW k i val 
        writeRef sum (f val) 


apply (Force p l) =
  \k -> do arr <- M.new l -- newArray_ (0,l-1)
           apply p  (VectorW arr)
           imm <- V.freeze arr
           forM_ [0..(fromIntegral l-1)] $ \ix ->
             -- do a <- readArray arr ix
                applyW k ix (imm V.! ix) 
        

---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

(<:) :: PushT m a -> (Ix -> a -> m ()) -> m () 
p <: k = apply p (ApplyW k)

use :: PrimMonad m => V.Vector a -> Length -> PushT m a
use mem l = Use mem l
-- undefunctionalised 
--  where
--    p k =
--      for_ (fromIntegral l) $ \ix ->
--      do
--        a <- read mem ix
--        k ix a 

map :: (a -> b) -> PushT m a -> PushT m b
map f p= Map p f

imap :: (a -> Ix -> b) -> PushT m a -> PushT m b
imap f p = IMap p f

ixmap :: (Ix -> Ix) -> PushT m a -> PushT m a
ixmap f p = IxMap p f

(++) :: (Monad m) =>  PushT m a -> PushT m a  -> PushT m a
p1 ++ p2 = Append (fromIntegral $ len p1) p1 p2  

reverse :: PushT m a -> PushT m a
reverse p = ixmap (\i -> (fromIntegral (len p - 1)) - i) p

iterate :: RefMonad m r => Length -> (a -> a) -> a -> PushT m a
iterate n f a = Iterate f a n

---------------------------------------------------------------------------
-- Conversion Pull Push (Clean this mess up)
---------------------------------------------------------------------------

push (Pull ixf n) =
  Generate ixf n

class ToPush m arr where
  toPush ::  arr a -> PushT m a

instance Monad m => ToPush m (PushT m) where
  toPush = id

---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: PrimMonad m => PushT m a -> m (V.Vector a)
freeze p =
  do
     arr <- M.new (len p) -- newArray_ (0,(len p)-1) 
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
-- Simple programs
---------------------------------------------------------------------------
input11 = Pull id 16
-- simple1 :: (Num a, Num ix, ForMonad ctxt ix m)
--          => Pull ix a -> PushT m ix a
simple1 = map (+1) . push 

runSimple1 = toVector (simple1 input11 :: PushT IO Int)


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
-- usePrg input = map (+1) (use input 10 )



-- class Monad m => MonadRef (ctxt :: * -> Constraint)  m r | m -> r, m -> ctxt where
--   newRef_ :: ctxt a => a -> m (r a)
--   readRef_ :: ctxt a => r a -> m a
--   writeRef_ :: ctxt a => r a -> a -> m ()


---------------------------------------------------------------------------
-- Experiments Push a -> Pull a
---------------------------------------------------------------------------

-- # Having indexing and conditionals in the expr type may help.

index_ :: (Monad m) => PushT m a -> Ix -> m a
index_ (Map p f) ix = liftM f (index_ p ix)
index_ (Generate ixf n) ix = return $ ixf ix
index_ (IMap p f) ix = liftM2 f (index_ p ix) (return ix) 
index_ (Iterate f a l) ix =
  do sum <- newRef a
     forM_ [0..ix-1] $ \i -> 
       do val <- readRef sum
          writeRef sum (f val)
     readRef sum
-- needs some work     
-- index_ (Append l p1 p2) ix =
--   do r <- mkRef_
--      cond (ix >* l)
--        (do a <- index_ p2 (return $ ix - l)
--            writeRef_ r a)
--        (do a <- index_ p1 (return $ ix) 
--            writeRef_ r a)
--      readRef_ r






-- {-# LANGUAGE MultiParamTypeClasses #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE TypeOperators #-}
-- {-# LANGUAGE GADTs #-}
-- {-# LANGUAGE UndecidableInstances #-}

-- {-# LANGUAGE ScopedTypeVariables #-}

-- module NoCompilePush where


-- import Control.Monad
-- import Control.Monad.ST
-- import Control.Monad.Primitive
-- import Data.RefMonad

-- import qualified Data.Vector as V
-- import qualified Data.Vector.Mutable as M 

-- import Prelude hiding (reverse,scanl)
-- import qualified Prelude as P 

-- ---------------------------------------------------------------------------

-- type Index = Int
-- type Length = Int 


-- ---------------------------------------------------------------------------
-- -- Pull array
-- ---------------------------------------------------------------------------

-- data Pull a = Pull (Index -> a) Length 

-- ---------------------------------------------------------------------------
-- -- Push array
-- --------------------------------------------------------------------------- 
-- data Push m a = Push ((Write a m) ~> m ()) Length 

-- data Write a m where
--   MapW :: Write b m -> (a -> b) -> Write a m
--   IMapW :: Write b m -> (a -> Index -> b) -> Write a m
--   IxMapW :: Write a m -> (Index -> Index) -> Write a m 
--   ApplyW :: (Index -> a -> m ()) -> Write a m

--   VectorW :: PrimMonad m => M.MVector (PrimState m) a -> Write a m

--   AppendW :: Write a m -> Index -> Write a m
--   Offset :: Write a m -> Length -> Write a m


-- applyW :: Write a m -> (Index -> a -> m ())
-- applyW (MapW k f) =  \i a -> applyW k i (f a)
-- applyW (IMapW k f) = \i a -> applyW k i (f a i)
-- applyW (IxMapW k f) = \i a -> applyW k (f i) a 
-- applyW (ApplyW k) = k

-- applyW (VectorW v) = \i a -> M.write v i a

-- applyW (AppendW k l) = \i a -> applyW k (l + i) a
-- applyW (Offset k n) = \i a -> applyW k (n + i) a    -- duplicate append


-- data a ~> b where
--   Map :: ((Write a m) ~> m ()) -> (a -> b) -> ((Write b m) ~> m ())
--   IMap :: ((Write a m) ~> m ()) -> (a -> Index -> b) -> ((Write b m) ~> m ())
--   Append :: Monad m => Index -> (Write a m ~> m ()) -> (Write a m ~> m ()) -> (Write a m ~> m ())
--   Generate :: Monad m => (Index -> a) -> Length -> ((Write a m) ~> m ())
--   Iterate :: RefMonad m r => (a -> a) -> a -> Length -> ((Write a m) ~> m ())
  
--   -- UnSafe
--   IxMap :: ((Write a m) ~> m ()) -> (Index -> Index) -> ((Write a m) ~> m ()) 
  
--   -- Seq :: Monad m => ((Write a m) ~> m ()) -> ((Write a m) ~> m ()) -> ((Write a m) ~> m ()) 
--   -- Scatter :: Monad m => (Index -> (a,Index)) -> Length -> ((Write a m) ~> m ())
--   -- Before  :: Monad m => ((Write b m) ~> m ()) -> ((Write b m) ~> m ()) -> ((Write b m) ~> m ()) 
--   -- Stride  :: Monad m => Index -> Length -> Length -> (Index -> a) -> ((Write a m) ~> m ())
  


-- apply :: (a ~> b) -> (a -> b)
-- apply (Map p f) = \k -> apply p (MapW k f)
-- apply (IMap p f) = \k -> apply p (IMapW k f)
-- apply (IxMap p f) = \k -> apply p (IxMapW k f) 
-- apply (Append l p1 p2) = \k -> apply p1 k >>
--                                apply p2 (AppendW k l)

-- apply (Generate ixf n) = (\k -> forM_ [0..(n-1)] $ \i ->
--                            applyW k i (ixf i))
-- apply (Iterate f a n) = \k ->
--   do
--     sum <- newRef a 
--     forM_ [0..(n-1)] $ \i ->
--       do
--         val <- readRef sum
--         applyW k i val 
--         writeRef sum (f val) 
        


-- {-
-- data F a m where
--   MapF :: F a m -> (a -> b) -> F b m

-- apply :: F a m -> ((Index -> a -> m ()) -> m ())
-- apply ....
-- -}

-- ---------------------------------------------------------------------------
-- -- Basic functions on push arrays
-- ---------------------------------------------------------------------------

-- len :: Push m a -> Length
-- len (Push _ n) = n

-- (<:) :: Push m a -> (Index -> a -> m ()) -> m () 
-- (Push p _) <: k = apply p (ApplyW k)

-- -- (<~:) :: Push m a -> Write a m ~> m () 
-- (Push p _) <~: k = apply p k


-- map :: (a -> b) -> Push m a -> Push m b
-- map f (Push p l) = Push (Map p f) l

-- imap :: (a -> Index -> b) -> Push m a -> Push m b
-- imap f (Push p l) = Push (IMap p f) l 

-- ixmap :: (Index -> Index) -> Push m a -> Push m a
-- ixmap f (Push p l) = Push (IxMap p f) l 

-- (++) :: Monad m =>  Push m a -> Push m a  -> Push m a
-- (Push p1 l1) ++ (Push p2 l2) = 
--   Push (Append l1 p1 p1) (l1 + l2) 

-- reverse :: Push m a -> Push m a
-- reverse p = ixmap (\i -> (len p - 1) - i) p

-- iterate :: RefMonad m r => Length -> (a -> a) -> a -> Push m a
-- iterate n f a = Push (Iterate f a n) n 
  
-- zipPull :: Pull a -> Pull b -> Pull (a,b)
-- zipPull (Pull p1 n1) (Pull p2 n2) = Pull (\i -> (p1 i, p2 i)) (min n1 n2) 


-- ---------------------------------------------------------------------------
-- -- Conversion Pull Push (Clean this mess up)
-- ---------------------------------------------------------------------------

-- push (Pull ixf n) =
--   Push (Generate ixf n) n  

-- class ToPush m arr where
--   toPush ::  arr a -> Push m a

-- instance Monad m => ToPush m (Push m) where
--   toPush = id

-- instance (PullFrom c, Monad m) => ToPush m c where
--   toPush = push . pullfrom

-- ---------------------------------------------------------------------------
-- -- Convert to Pull array
-- --------------------------------------------------------------------------- 
-- class PullFrom c where
--   pullfrom :: c a -> Pull a

-- instance PullFrom V.Vector where
--   pullfrom v = Pull (\i -> v V.! i ) (V.length v)

-- instance PullFrom [] where 
--   pullfrom as = Pull (\i -> as !! i) (length as) 

-- instance PullFrom Pull where
--   pullfrom = id 

-- ---------------------------------------------------------------------------
-- -- write to vector
-- --------------------------------------------------------------------------- 

-- freeze :: PrimMonad m => Push m a -> m (V.Vector a)
-- freeze (Push p l) =
--   do
--      arr <- M.new l
--      apply p (VectorW arr) 
--      V.freeze arr 


-- ---------------------------------------------------------------------------
-- -- Simple program
-- ---------------------------------------------------------------------------

-- input1 = Pull (\i -> i) 128 

-- test1 :: Monad m => Pull Int -> Push m Int
-- test1 = reverse . push  

-- runTest1 = freeze (test1 input1 :: Push IO Int) 




-- ---------------------------------------------------------------------------
-- -- Push to Pull (should be easy here)
-- ---------------------------------------------------------------------------
