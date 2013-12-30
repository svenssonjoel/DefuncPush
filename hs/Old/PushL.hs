{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE ScopedTypeVariables #-}

module Push where


import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
{- package TypeCompose -}
import Data.RefMonad

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M 

import Prelude hiding (reverse,zip,concat,map,scanl,replicate,repeat, (++) ) 

import qualified Prelude as P 
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

data Push m a =
  -- Push ((Either () (Index -> a -> m ())) -> m (Either Length ()))
  Push ((Index -> a -> m ()) -> m ()) (m Length) 
  -- Thought: Left input -> Left output
  --          Right input -> Right output 

---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

len :: Monad m => Push m a -> m Length
len (Push p l) = l 
 

(<:) :: Push m a -> (Index -> a -> m ()) -> m ()
(Push p l) <: f = p f 

(++) :: Monad m => Push m a -> Push m a  -> Push m a
Push p1 l1 ++ Push p2 l2 = Push q l
  where
    q k = do

      l1' <- l1 
           
      p1 k
      p2 $ \i a -> k (l1' + i) a
    l = do
      l1' <- l1
      l2' <- l2
      return $ l1' + l2' 





ixmap :: Monad m => (Index -> m Index) -> Push m a -> Push m a
ixmap f p = Push q (len p) 
  where
    q k =
      p <: \i a ->
      do
        i' <- f i
        k i' a 
    


reverse :: Monad m => Push m a -> Push m a
reverse p = ixmap (\i ->
                    do
                      l <- len p
                      return $ (l - 1) - i) p



instance (PrimMonad m, RefMonad m r) => Monad (Push m) where
  return a = Push  (\k -> k 0 a) (return 1)
      
  p >>= f = Push p' l
    where
      p' k = do r <- newRef 0
                p <: ( \i a ->
                        do s <- readRef r
                           let (Push q m) = (f a)
                           q (\j b -> k (s + j) b)
                           m' <- m
                           writeRef r (s + m'))
      l = do r <- newRef 0
             p <: ( \_ a -> 
               do let (Push q n') = f a
                  n  <- n'
                  modifyRef r (+n))
             readRef r
                  






            

-- [1,2,3] -> [1,2,2,3,3,3]
repeat :: (RefMonad m r, PrimMonad m) => Push m Int -> Push m Int 
repeat p = p >>= (\a -> replicate a a)

replicate :: (RefMonad m r, PrimMonad m) => Int -> a -> Push m a 
replicate n a = Push p (return n)
  where
    p k = forM_ [0..n-1] $ \i -> k i a
                   
  
                     
    
 
 ---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: PrimMonad m => Push m a -> m (V.Vector a)
freeze (Push p n) =
  do
     s  <- n -- compute the length 
     arr <- M.new s
     p (\i a -> M.write arr i a)
     V.freeze arr 

push (Pull ixf n) =
  Push (\k -> forM_ [0..(n-1)] $ \i ->
         k i (ixf i) ) (return n)

---------------------------------------------------------------------------
-- Simple program
---------------------------------------------------------------------------

input1 = Pull (\i -> i) 128 

test1 :: Monad m => Pull Int -> Push m Int
test1 = reverse . push  

runTest1 = freeze (test1 input1 :: Push IO Int)


input2 = Pull (\i -> i) 10

test2 :: Monad m => Pull Int -> Push m Int
test2 a = p ++ p 
  where
    p = push  a

runTest2 = freeze (test2 input2 :: Push IO Int) 
 

---------------------------------------------------------------------------
--
---------------------------------------------------------------------------

input10 = Pull (\i -> i) 5

test10 :: (RefMonad m r, PrimMonad m) => Pull Int -> Push m Int
test10 = repeat . push  

runTest10 = freeze (test10 input10 :: Push IO Int) 

