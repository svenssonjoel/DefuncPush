{-# LANGUAGE ScopedTypeVariables #-}

import PushFS

import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
import Data.RefMonad

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M 

import Prelude hiding (reverse,scanl,(++))
import qualified Prelude as P

import Pull
---------------------------------------------------------------------------
-- Simple program
---------------------------------------------------------------------------

input1 = Pull (\i -> i) 128 

test1 :: Monad m => Pull Int -> Push m Int
test1 = reverse . push  

runTest1 = freeze (test1 input1 :: Push IO Int) 


---------------------------------------------------------------------------
-- zip test
---------------------------------------------------------------------------
i1 = Pull (\i -> i) 32
i2 = Pull (\i -> i + 32) 32

test2 :: Monad m => Pull Int -> Pull Int -> Push m Int
test2 a1 a2 = zipByStride a1 a2

test2b :: Monad m => Pull Int -> Pull Int -> Push m Int
test2b a1 a2 = zipByPermute (toPush a1) (toPush a2)


runTest2 = freeze (test2 i1 i2 :: Push IO Int)
runTest2b = freeze (test2b i1 i2 :: Push IO Int) 


---------------------------------------------------------------------------
-- Flatten test
---------------------------------------------------------------------------

i :: (RefMonad m r, PrimMonad m) => Pull (Push m Int) 
i = pullFrom (P.map (toPush . pullFrom) [[1,2,3],[4,5],[6]])

test3 :: (RefMonad m r, PrimMonad m) => Pull (Push m Int) -> Push m Int
test3 p = flatten p 

runTest3 = freeze (test3 i :: Push IO Int)

---------------------------------------------------------------------------
-- Bind test
---------------------------------------------------------------------------

pinput :: (PrimMonad m, RefMonad m r) => Push m Int
pinput = toPush [1,2,3,4] 

test4 :: forall m r . (RefMonad m r, PrimMonad m) => Push m Int ->  Push m Int
test4 p = p >>= (\a -> (toPush [a,a,a] :: Push m Int) ) 

runTest4 = freeze (test4 pinput :: Push IO Int) 


---------------------------------------------------------------------------
-- Stride test (Stride is not entirely correct) 
---------------------------------------------------------------------------

sinput :: Pull Int
sinput = pullFrom [1..9]

test5 :: Monad m => Pull Int -> Push m Int
test5 arr =  (toPush (pullFrom (replicate 45 0))) `before` stride 0 5 arr

test5b :: Monad m => Pull Int -> Push m Int
test5b arr =  (toPush (pullFrom (replicate 29 0))) `before` stride 2 3 arr


runTest5 = freeze (test5 sinput :: Push IO Int)
runTest5b = freeze (test5b sinput :: Push IO Int)


---------------------------------------------------------------------------
-- Test Fold
---------------------------------------------------------------------------
-- i6 :: (RefMonad m r, PrimMonad m) => Push m Int
-- i6 = (toPush . pullFrom) [1,2,3,4,5,6]

-- test6 :: (RefMonad m r, PrimMonad m) => Push m Int -> m Int
-- test6 p = foldPush (+) 0 p 

-- runTest6 = test6 i6 :: IO Int

---------------------------------------------------------------------------
-- Test scanlPush
---------------------------------------------------------------------------
-- i7 :: (RefMonad m r, PrimMonad m) => Push m Int
-- i7 = (toPush . pullFrom) [1,2,3,4,5,6,7,8,9,10]

-- test7 :: (RefMonad m r, PrimMonad m) => Push m Int -> Push m Int 
-- test7 p = scanlPush  (+) 0 p 

-- runTest7 = freeze $ (test7 i7 :: Push IO Int)


---------------------------------------------------------------------------
-- Test unpairP
---------------------------------------------------------------------------
i8 :: (RefMonad m r, PrimMonad m) => Push m (Int,Int)
i8 = (toPush . pullFrom) [(1,2),(3,4),(5,6),(7,8),(9,10)]

test8 :: (RefMonad m r, PrimMonad m) => Push m (Int,Int) -> Push m Int 
test8 p = unpairP  p 

runTest8 = freeze $ (test8 i8 :: Push IO Int)

---------------------------------------------------------------------------
-- Another test of scanlPush
---------------------------------------------------------------------------
-- i9_1_1,i9_1_2, i9_2_1, i9_2_2,i9_1,i9_2 :: (RefMonad m r, PrimMonad m) => Push m Int
-- i9_1_1 = (toPush . pullFrom) [1,2,3,4,5] 
-- i9_1_2 = (toPush . pullFrom) [6,7,8,9,10]
-- i9_2_1 = (toPush . pullFrom) [1,3,5,7,9] 
-- i9_2_2 = (toPush . pullFrom) [2,4,6,8,10]
-- i9_1 = i9_1_1 ++ i9_1_2
-- i9_2 = interleave i9_2_1 i9_2_2

-- test9 p = scanlPush (+) 0 p

-- runTest9 = do v1 <- runTest (test9 i9_1)
--               v2 <- runTest (test9 i9_2)
--               return (v1 == v2)

-- -- Generic test runner

-- runTest p = freeze $ (p :: Push IO Int)

