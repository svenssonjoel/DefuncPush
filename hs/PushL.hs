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
  Push ((Either () (Index -> a -> m ())) -> m (Either Length ())) 
  -- Thought: Left input -> Left output
  --          Right input -> Right output 

---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

len :: Monad m => Push m a -> m Length
len (Push p) =
  do
    (Left n) <- p (Left ())
    return n 
 


(++) :: Monad m => Push m a -> Push m a  -> Push m a
Push p1 ++ Push p2 = Push q
  where
    q (Left ()) = do
      (Left l1) <- p1 (Left ())
      (Left l2) <- p2 (Left ())
      return $ Left (l1 + l2)
    q (Right k) = do
      (Left l1) <- p1 (Left ())
      -- l2 <- len p2 
           
      p1 $ Right k
      p2 $ Right $ \i a -> k (l1 + i) a
      return (Right ())





ixmap :: Monad m => (Index -> m Index) -> Push m a -> Push m a
ixmap f (Push p) = Push q
  where
    q (Left ()) = p (Left ())
  
    q (Right k) =
      p $ Right $ \i a ->
      do
        i' <- f i
        k i' a 
    


reverse :: Monad m => Push m a -> Push m a
reverse p = ixmap (\i ->
                    do
                      l <- len p
                      return $ (l - 1) - i) p



instance (PrimMonad m, RefMonad m r) => Monad (Push m) where
  return a = Push $ \k -> case k of
                            (Right k') -> do
                                            res <- (k' 0 a)
                                            return $ Right res 
                            (Left ())  -> return $ Left 1 
  (Push p) >>= f = Push p'
    where
      p' (Right k') = do r <- newRef 0
                         p $ Right $ \i a ->
                           do s <- readRef r
                              let (Push q) = (f a)
                              q $ Right (\j b -> k' (s + j) b)
                              (Left m') <- q (Left ()) 
                              writeRef r (s + m')
      p' (Left ()) = do r <- newRef 0
                        p $ Right $ \_ a -> 
                          do let (Push q) = f a
                             (Left n)  <- q (Left ())    
                             modifyRef r (+n)
                        nl <-readRef r
                        return (Left nl) 





      -- l' = 
            

-- [1,2,3] -> [1,2,2,3,3,3]
repeat :: (RefMonad m r, PrimMonad m) => Push m Int -> Push m Int 
repeat p = p >>= (\a -> replicate a a)

replicate :: (RefMonad m r, PrimMonad m) => Int -> a -> Push m a 
replicate n a = Push p -- (\k -> ) n 
  where
    p (Right k) = do forM_ [0..n-1] $ \i -> k i a
                     return (Right ())
    p (Left ()) = return (Left n) 
                     
    
 
 ---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: PrimMonad m => Push m a -> m (V.Vector a)
freeze (Push p) =
  do
     (Left s)  <- p (Left ())
     arr <- M.new s
     p $ Right (\i a -> M.write arr i a)
     V.freeze arr 

push (Pull ixf n) =
  Push $ \k ->
         case k of
           Right k' -> do forM_ [0..(n-1)] $ \i ->
                             k' i (ixf i)
                          return $ Right ()
           Left () -> return $ Left n 

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

