{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

module PushF where


import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
import Data.RefMonad

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M 

import Prelude hiding (reverse) 

---------------------------------------------------------------------------

type Index = Int
type Length = Int 


---------------------------------------------------------------------------
-- Pull array
---------------------------------------------------------------------------

data Pull a = Pull (Index -> a) Length 

---------------------------------------------------------------------------
-- Push array
--------------------------------------------------------------------------- 
data Push m a = Push ((Write a m) ~> m ()) Length 

data Write a m where
  MapW :: Write b m -> (a -> b) -> Write a m
  IMapW :: Write b m -> (a -> Index -> b) -> Write a m
  IxMapW :: Write a m -> (Index -> Index) -> Write a m 
  ApplyW :: (Index -> a -> m ()) -> Write a m
  AppendW :: Write a m -> Index -> Write a m
  VectorW :: PrimMonad m => M.MVector (PrimState m) a -> Write a m

  Offset :: Write a m -> Length -> Write a m
  

  BindW :: RefMonad m r => Length -> (a -> ((Write b m) ~> m (),Length)) -> Write b m -> r Index -> Write a m
  BindW2 :: Write a m -> Index -> Write a m
  BindLength :: RefMonad m r => (a -> Length) -> r Index -> Write a m


applyW :: Write a m -> (Index -> a -> m ())
applyW (MapW k f) =  \i a -> applyW k i (f a)
applyW (IMapW k f) = \i a -> applyW k i (f a i)
applyW (IxMapW k f) = \i a -> applyW k (f i) a 
applyW (ApplyW k) = k
applyW (AppendW k l) =  \i a -> applyW k (l + i) a
applyW (VectorW v) = \i a -> M.write v i a

applyW (Offset k n) = \i a -> applyW k (n + i) a    -- duplicate append


applyW (BindW l f k r) = \i a -> do s <- readRef r
                                    let (q,m) = (f a)
                                    apply q (BindW2 k s)
                                    writeRef r (s + m)
applyW (BindW2 k s) = \j b -> applyW k (s + j) b    -- duplicate append again
applyW (BindLength f r) = \_ a -> do let l'' = f a
                                     modifyRef r (+l'')


data a ~> b where
  Map :: ((Write a m) ~> m ()) -> (a -> b) -> ((Write b m) ~> m ())
  IMap :: ((Write a m) ~> m ()) -> (a -> Index -> b) -> ((Write b m) ~> m ())
  IxMap :: ((Write a m) ~> m ()) -> (Index -> Index) -> ((Write a m) ~> m ()) 
  Append :: Monad m => Index -> (Write a m ~> m ()) -> (Write a m ~> m ()) -> (Write a m ~> m ())
  Generate :: Monad m => (Index -> a) -> Length -> ((Write a m) ~> m ())
  Iterate :: RefMonad m r => (a -> a) -> a -> Length -> ((Write a m) ~> m ())
  Unpair :: Monad m => (Index -> (a,a)) -> Length -> ((Write a m) ~> m ())
  Return :: a -> ((Write a m) ~> m ())
  Bind :: RefMonad m r => ((Write a m) ~> m ()) -> Length -> (a -> ((Write b m) ~> m (),Length)) -> ((Write b m) ~> m ())

  Scatter :: Monad m => (Index -> (a,Index)) -> Length -> ((Write a m) ~> m ())
  Before  :: Monad m => ((Write b m) ~> m ()) -> ((Write b m) ~> m ()) -> ((Write b m) ~> m ()) 

  Flatten :: Monad m => (Index -> ((Write a m) ~> m ())) -> [Length] -> Length -> ((Write a m) ~> m ()) 
  Stride  :: Monad m => Index -> Length -> Length -> (Index -> a) -> ((Write a m) ~> m ())

apply :: (a ~> b) -> (a -> b)
apply (Map p f) = \k -> apply p (MapW k f)
apply (IMap p f) = \k -> apply p (IMapW k f)
apply (IxMap p f) = \k -> apply p (IxMapW k f) 
apply (Append l p1 p2) = \k -> apply p1 k >>
                               apply p2 (AppendW k l)

apply (Generate ixf n) = (\k -> forM_ [0..(n-1)] $ \i ->
                           applyW k i (ixf i))
apply (Iterate f a n) = \k ->
  do
    sum <- newRef a 
    forM_ [0..(n-1)] $ \i ->
      do
        val <- readRef sum
        applyW k i val 
        writeRef sum (f val) 
        
apply (Unpair f n) = \k -> forM_ [0..(n-1)] $ \i ->
                             applyW k (i*2) (fst (f i)) >>
                             applyW k (i*2+1) (snd (f i))
apply (Return a) = \k -> applyW k 0 a
apply (Bind p l f) = \k -> do r <- newRef 0
                              apply p (BindW l f k r)


apply (Scatter f n) = \k -> forM_ [0..(n-1)] $ \i ->
                              applyW k (snd (f i)) (fst (f i))
apply (Before p1 p2) = \k -> apply p1 k >> apply p2 k 

apply (Flatten p lengths n) =
  \k -> forM_ [0..n-1] $ \i ->
  do
    forM_ [0..(lengths !! i)-1] $ \elem ->
      let k' = Offset k (sm !! i) 
      in  apply (p i) k'
  where sm   = scanl (+) 0 lengths 
apply (Stride start step n f) =
  \k -> forM_ [0..n-1] $ \i ->
         applyW k (start + step*i) (f i) 



{-
data F a m where
  MapF :: F a m -> (a -> b) -> F b m

apply :: F a m -> ((Index -> a -> m ()) -> m ())
apply ....
-}

---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

len :: Push m a -> Length
len (Push _ n) = n

(<:) :: Push m a -> (Index -> a -> m ()) -> m () 
(Push p _) <: k = apply p (ApplyW k)

map :: (a -> b) -> Push m a -> Push m b
map f (Push p l) = Push (Map p f) l

imap :: (a -> Index -> b) -> Push m a -> Push m b
imap f (Push p l) = Push (IMap p f) l 

ixmap :: (Index -> Index) -> Push m a -> Push m a
ixmap f (Push p l) = Push (IxMap p f) l 

(++) :: Monad m =>  Push m a -> Push m a  -> Push m a
(Push p1 l1) ++ (Push p2 l2) = 
  Push (Append l1 p1 p1) (l1 + l2) 

reverse :: Push m a -> Push m a
reverse p = ixmap (\i -> (len p - 1) - i) p

iterate :: RefMonad m r => Length -> (a -> a) -> a -> Push m a
iterate n f a = Push (Iterate f a n) n 

unpair :: Monad m => Pull (a,a) -> Push m a
unpair (Pull ixf n) =
  Push (Unpair ixf n) (2*n)

zipPush :: Monad m => Pull a -> Pull a -> Push m a
zipPush p1 p2 = unpair $  zipPull p1 p2 
  
zipPull :: Pull a -> Pull b -> Pull (a,b)
zipPull (Pull p1 n1) (Pull p2 n2) = Pull (\i -> (p1 i, p2 i)) (min n1 n2) 

scatter :: Monad m => Pull (a,Index) -> Push m a
scatter (Pull ixf n) =
  Push (Scatter ixf n) n 

-- combine effects of two push arrays. The second may overwrite the first.
before :: Monad m => Push m a -> Push m a -> Push m a
before (Push p1 n1) (Push p2 n2) =
    Push (Before p1 p2) (max n1 n2) 



-- Complicated case
flatten :: Monad m => Pull (Push m a) -> Push m a
flatten (Pull ixf n) =
  Push (Flatten (pFun . ixf) lengths n) (last sm)
    where lengths = [len (ixf i) | i <- [0..n-1]]
          sm   = scanl (+) 0 lengths 
          pFun (Push p _) = p 

--                   start     step
stride :: Monad m => Index -> Length -> Pull a -> Push m a 
stride start step (Pull ixf n) =
  Push (Stride start step n ixf) m
  where m = start + n*step


zipByStride :: Monad m => Pull a -> Pull a -> Push m a
zipByStride p1 p2 = stride 0 2 p1 `before` stride 1 2 p2 



instance (PrimMonad m, RefMonad m r) => Monad (Push m) where
  return a = Push (Return a) 1
  (Push p l) >>= f = Push p' l'
    where
      -- A trick so that the data types don't depend on the type Push
      g a = let (Push p l) = f a in (p,l)
      h a = let (Push _ l) = f a in l
      p' = Bind p l g
      l' = unsafeInlinePrim $
           do r <- newRef 0
              apply p (BindLength h r)
              readRef r


---------------------------------------------------------------------------
-- Conversion Pull Push
---------------------------------------------------------------------------

push (Pull ixf n) =
  Push (Generate ixf n) n  

class ToPush m arr where
  toPush ::  arr a -> Push m a

instance Monad m => ToPush m (Push m) where
  toPush = id

instance Monad m => ToPush m Pull where
  toPush = push 

instance Monad m => ToPush m V.Vector where
  toPush = toPush . pullfrom


pullfrom :: V.Vector a -> Pull a
pullfrom v = Pull (\i -> v V.! i ) (V.length v) 

---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: PrimMonad m => Push m a -> m (V.Vector a)
freeze (Push p l) =
  do
     arr <- M.new l
     apply p (VectorW arr) -- Big questionmark here
     V.freeze arr 


---------------------------------------------------------------------------
-- Simple program
---------------------------------------------------------------------------

input1 = Pull (\i -> i) 128 

test1 :: Monad m => Pull Int -> Push m Int
test1 = reverse . push  

runTest1 = freeze (test1 input1 :: Push IO Int) 




---------------------------------------------------------------------------
--
---------------------------------------------------------------------------
