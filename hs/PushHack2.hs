

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
             deriving Show 
data LengthDone = LinearD Int
                | AddD Int LengthDone LengthDone
                deriving Show


-- thought
data L = Base Int
       | AddL (Maybe Int) L L
       deriving Show
{-
   Freeze computes all "uncomputed lengths.
   Programs that needs to compute lengths, does so.
     But that will mean that the Length recipie needs to depend on
     the push array computation. 
-} 

                

getL :: LengthDone -> Int
getL (LinearD i) = i
getL (AddD i _ _) = i 

data Push m a = Push ((LengthDone -> Int -> a -> m ()) -> m ()) (m LengthC)


---------------------------------------------------------------------------
-- Helpful pull arrays
---------------------------------------------------------------------------

data Pull a = Pull (Int -> a) Int

push (Pull ixf n) =
  Push  (\k -> forM_ [0..(n -1)] $ \i ->
         k (LinearD n) i (ixf i) ) (return (Linear n))


---------------------------------------------------------------------------
-- Library
--------------------------------------------------------------------------- 
(++) (Push p1 l1) (Push p2 l2) = Push q (do l1' <- l1
                                            l2' <- l2
                                            return (Add l1' l2'))
  where
    q k = do p1 k
             p2 (\ (AddD _ l1 l2) i a -> k l2 (i + getL l1) a)

map ::  (a -> b) -> Push m a -> Push m b
map f (Push p l) = Push (\k -> p (\ld i a -> k ld i (f a)) ) l

concat :: (RefMonad m r, Monad m) => Push m (Push m a) -> Push m a
concat (Push p l) = Push q l'
  where
    -- Still recalculates lengths
    q k = do r <- newRef (LinearD 0)
             p $ \rl i a ->
               do s <- readRef r
                  let (Push q' m) = a
                  q' (\ldq' j b -> do
                         writeRef r (AddD (getL s + getL ldq')  ldq' s)
                         k ldq' ((getL s) + j) b)
                  


    -- Create a recipie 
    l' = do r <- newRef (Linear 0)
            p $ \_ i a ->
              do
                s <- readRef r
                let (Push q' m) = a
                m' <- m 
                writeRef r (Add m' s) -- (Add a1 (Add a2 (Add a3 (Linear 0))))
            readRef r
            
-- prefer some other structure !  (where this "works") 
getNth 0 (LinearD n) = LinearD n
getNth 0 (AddD _ a b) = a
getNth n (AddD _ a b) = getNth (n-1) b
getNth n (LinearD i) = error $ "Linear " P.++ show i

repeat :: Monad m => Push m Int -> Push m (Push m Int)
repeat = map (\a -> replicate a a) 

-- Dont know what will happen here !
replicate :: Monad m => Int -> a -> Push m a
replicate n a = Push (\k -> forM_ [0..(n - 1)] $ \ix -> k (LinearD n) ix a ) (return (Linear n) )

computeLength :: Monad m => LengthC -> m LengthDone
computeLength (Linear i) = return $ LinearD i
computeLength (Add l1 l2) =
  do
    l1' <- computeLength l1
    l2' <- computeLength l2
    let i1 = getL l1'
        i2 = getL l2'
    
    return $ AddD (i1+i2) l1' l2'

freeze :: PrimMonad m => Push m a -> m (V.Vector a)
freeze (Push p n) =
  do
     n' <- n 
     l' <- computeLength n'
     let s  = getL l' 
     
     arr <- M.new s
     p (\l' i a -> M.write arr i a)
     V.freeze arr 

input2 = Pull (\i -> i) 10

test2 :: Monad m => Pull Int -> Push m Int
test2 a = p ++ p 
  where
    p = push  a

runTest2 = freeze (test2 input2 :: Push IO Int) 


input3 = Pull (\i -> i) 10

test3 :: (RefMonad m r, Monad m) => Pull Int -> Push m Int
test3 a = concat (repeat p)
  where
    p = push  a

runTest3 = freeze (test3 input3 :: Push IO Int) 

