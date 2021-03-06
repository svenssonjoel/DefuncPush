

module PushHack where


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
-- Strange Push arrays
---------------------------------------------------------------------------

data LengthC = Linear Int
             | Add LengthC LengthC

data LengthDone = LinearD Int
                | AddD Int LengthDone LengthDone

getL :: LengthDone -> Int
getL (LinearD i) = i
getL (AddD i _ _) = i 

data Push m a = Push (LengthDone -> (Int -> a -> m ()) -> m ()) LengthC 


---------------------------------------------------------------------------
-- Helpful pull arrays
---------------------------------------------------------------------------

data Pull a = Pull (Int -> a) Int

push (Pull ixf n) =
  Push  (\l k -> forM_ [0..(getL l -1)] $ \i ->
         k i (ixf i) ) (Linear n)


---------------------------------------------------------------------------
-- Library
--------------------------------------------------------------------------- 
(++) (Push p1 l1) (Push p2 l2) = Push q (Add l1 l2)
  where
    q (AddD m l1 l2) k = do p1 l1 k
                            p2 l2 (\i a -> k (i + getL l1) a)

map ::  (a -> b) -> Push m a -> Push m b
map f (Push p l) = Push (\ ld k -> p ld (\i a -> k i (f a)) ) l

-- concat :: Push m (Push m a) -> Push m a
-- concat (Push p l) = Push q l'
--   where
--     q rl k = do r <- newRef (Linear 0)
--                 p l $ \i a ->
--                   do s <- readRef r
--                      let (Push q' m) = a
--                      q' (\j b -> k (Add s j) b)
--                      writeRef r (Add s + m)
--     l' = undefined 
               

repeat :: Monad m => Push m Int -> Push m (Push m Int)
repeat = map (\a -> replicate a a) 

-- Dont know what will happen here !
replicate :: Monad m => Int -> a -> Push m a
replicate n a = Push (\l k -> forM_ [0..(getL l - 1)] $ \ix -> k ix a ) (Linear n) 

computeLength :: LengthC -> LengthDone
computeLength (Linear i) = LinearD i
computeLength (Add l1 l2) = AddD (i1+i2) l1' l2'
  where
    l1' = computeLength l1
    l2' = computeLength l2
    i1  = getL l1'
    i2  = getL l2'

freeze :: PrimMonad m => Push m a -> m (V.Vector a)
freeze (Push p n) =
  do
     let l' = computeLength n 
         s  = getL l' 
     
     arr <- M.new s
     p l' (\i a -> M.write arr i a)
     V.freeze arr 



input2 = Pull (\i -> i) 10

test2 :: Monad m => Pull Int -> Push m Int
test2 a = p ++ p 
  where
    p = push  a

runTest2 = freeze (test2 input2 :: Push IO Int) 
 
