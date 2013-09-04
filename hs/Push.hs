{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Push where


import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
{- package TypeCompose -}
import Data.RefMonad

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M 

import Prelude hiding (reverse,zip,concat,map,scanl) 

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
data Push m a = Push ((Index -> a -> m ()) -> m ()) Length 



---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

len :: Push m a -> Length
len (Push _ n) = n


(<:) :: Push m a -> (Index -> a -> m ()) -> m () 
(Push p _) <: k = p k 

map :: (a -> b) -> Push m a -> Push m b
map f (Push p l) = Push (\k -> p (\i a -> k i (f a))) l

imap :: (a -> Index -> b) -> Push m a -> Push m b
imap f (Push p l) = Push (\k -> p (\i a -> k i (f a i))) l 

ixmap :: (Index -> Index) -> Push m a -> Push m a
ixmap f (Push p l) = Push (\k -> p (\i a -> k (f i) a)) l 

(++) :: Monad m =>  Push m a -> Push m a  -> Push m a
p1 ++ p2 = 
  Push (\k -> p1 <: k >>
              p2 <: (\i a -> k (len p1 + i) a)
       ) (len p1 + len p2) 

reverse :: Push m a -> Push m a
reverse p = ixmap (\i -> (len p - 1) - i) p

iterate :: Monad m => Length -> (a -> a) -> a -> Push m a
iterate n f a = Push (\k ->
                       forM_ [0..(n-1)] $ \i -> 
                         k i ((Prelude.iterate f a) !! i)  
                       ) n


unpair :: Monad m => Pull (a,a) -> Push m a
unpair (Pull ixf n) =
  Push (\k ->
         forM_ [0..(n-1)] $ \i ->
           k (i*2) (fst (ixf i)) >>
           k (i*2+1) (snd (ixf i))) (2*n)

zipPush :: Monad m => Pull a -> Pull a -> Push m a
zipPush p1 p2 = unpair $  zipPull p1 p2 

  
zipPull :: Pull a -> Pull b -> Pull (a,b)
zipPull (Pull p1 n1) (Pull p2 n2) = Pull (\i -> (p1 i, p2 i)) (min n1 n2) 

instance (PrimMonad m, RefMonad m r) => Monad (Push m) where
  return a = Push (\k -> k 0 a) 1
  (Push p l) >>= f = Push p' l'
    where
      p' k' = do r <- newRef 0
                 p $ \i a ->
                   do s <- readRef r
                      let (Push q m) = (f a)
                      q (\j b -> k' (s + j) b)
                      writeRef r (s + m)
      l' = unsafeInlinePrim $
           do r <- newRef 0
              p $ \_ a -> 
                do let (Push _ l'') = f a
                   modifyRef r (+l'')
              readRef r

scatter :: Monad m => Pull (a,Index) -> Push m a
scatter (Pull ixf n) =
  Push (\k ->
         forM_ [0..(n-1)] $ \i ->
           k (snd (ixf i)) (fst (ixf i))) n 


-- combine effects of two push arrays. The second may overwrite the first.
before :: Monad m => Push m a -> Push m a -> Push m a
before (Push p1 n1) (Push p2 n2) =
  Push (\k -> p1 k >> p2 k) (max n1 n2)



flatten :: Monad m => Pull (Push m a) -> Push m a
flatten (Pull ixf n) =
  Push (\k ->
         forM_ [0..n-1] $ \i ->
             let (Push p m) = ixf i
                 k' j a = k (sm !! i + j) a
             in  p k') (last sm)
             
             

  where lengths = [len (ixf i) | i <- [0..n-1]]
        sm   = scanl (+) 0 lengths 


--                   start     step
stride :: Monad m => Index -> Length -> Pull a -> Push m a 
stride start step (Pull ixf n) =
  Push (\k ->
         forM_ [0..n-1] $ \i ->
          k (start + step*i) (ixf i)  ) m
  where m = (start + n*step) - 1


zipByStride :: Monad m => Pull a -> Pull a -> Push m a
zipByStride p1 p2 = stride 0 2 p1 `before` stride 1 2 p2 

zipByPermute :: Monad m => Push m a -> Push m a -> Push m a
zipByPermute p1 p2 =
  Push (\k -> p1' <: k >> p2' <: k)  (2*(min (len p1) (len p2))) 
  where
    p1' = ixmap (\i -> i*2) p1
    p2' = ixmap (\i -> i*2+1) p2 


scanl :: (PullFrom c, RefMonad m r) => (a -> b -> a) -> a -> c b -> Push m a
scanl f init v = Push g l
  where
    (Pull ixf n) = pullfrom v
    l = n -- length v
    g k = do s <- newRef init
             forM_ [0..l-1] $ \ix -> do
               modifyRef s (`f` (ixf ix))
               readRef s >>= k ix
---------------------------------------------------------------------------
-- Conversion Pull Push
---------------------------------------------------------------------------

push (Pull ixf n) =
  Push (\k -> forM_ [0..(n-1)] $ \i ->
         k i (ixf i)) n 

class ToPush m arr where
  toPush ::  arr a -> Push m a

instance Monad m => ToPush m (Push m) where
  toPush = id

instance Monad m => ToPush m Pull where
  toPush = push 

instance (PullFrom c, Monad m) => ToPush m c  where
  toPush = push . pullfrom

---------------------------------------------------------------------------
-- Convert to Pull array
--------------------------------------------------------------------------- 
class PullFrom c where
  pullfrom :: c a -> Pull a

instance PullFrom V.Vector where
  pullfrom v = Pull (\i -> v V.! i ) (V.length v)

instance PullFrom [] where 
  pullfrom as = Pull (\i -> as !! i) (length as) 

instance PullFrom Pull where
  pullfrom = id 

---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: PrimMonad m => Push m a -> m (V.Vector a)
freeze (Push p l) =
  do
     arr <- M.new l
     p (\i a -> M.write arr i a)
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
