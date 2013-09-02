{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Push where


import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M 

import Prelude hiding (reverse,zip) 

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
