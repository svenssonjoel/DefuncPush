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

import Prelude hiding (reverse,zip,concat,map,scanl,replicate,repeat ) 

import qualified Prelude as P 
---------------------------------------------------------------------------

type Index = Int
type Length = Int 


---------------------------------------------------------------------------
-- Pull array
---------------------------------------------------------------------------

data Pull a = Pull (Index -> a) Length


computePull :: PrimMonad m => Pull a -> m (V.Vector a)
computePull (Pull f n) =
  do mem <- M.new n
     forM_ [0..n-1] $ \ix ->
       M.write mem ix (f ix)
     V.freeze mem


--  arr <- M.new l
--     p (\i a -> M.write arr i a)
--     V.freeze arr 


---------------------------------------------------------------------------
-- Push array
--------------------------------------------------------------------------- 
data Push m a =
  Push ((Index -> a -> m ()) -> m ()) Length 



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
  
unpairP :: Monad m => Push m (a,a) -> Push m a
unpairP (Push p n) =
  Push p' (2*n)
  where p' =
          \k ->
          let k' i (a,b) = k (i*2) a >> k (i*2+1) b
          in p k'  
          
interleave :: Monad m => Push m a -> Push m a -> Push m a
interleave (Push p m) (Push q n) = Push r (2 * (min m n))
  where r k = do p (\i a -> k (2*i) a)
                 q (\i a -> k (2*i+1) a)


---------------------------------------------------------------------------
-- Zip (added a special zip)
--------------------------------------------------------------------------- 
zipPush :: Monad m => Pull a -> Pull a -> Push m a
zipPush p1 p2 = unpair $  zipPull p1 p2 

zipSpecial :: Monad m => Push m a -> Pull b -> Push m (a,b)
zipSpecial (Push p n1) (Pull ixf n2) =
  Push p' (min n1 n2)
  where
    p' = \k ->
      let k' = \i a -> k i (a, ixf i)
      in p k'

    
zipPull :: Pull a -> Pull b -> Pull (a,b)
zipPull (Pull p1 n1) (Pull p2 n2) = Pull (\i -> (p1 i, p2 i)) (min n1 n2) 


-- [1,2,3] -> [1,2,2,3,3,3]
repeat :: (RefMonad m r, PrimMonad m) => Push m Int -> Push m Int 
repeat p = p >>= (\a -> replicate a a)

replicate :: (RefMonad m r, PrimMonad m) => Int -> a -> Push m a 
replicate n a = Push (\k -> forM_ [0..n-1] $ \i -> k i a) n 

---------------------------------------------------------------------------
-- Monad
---------------------------------------------------------------------------
instance (PrimMonad m, RefMonad m r) => Monad (Push m) where
  return a = Push (\k -> k 0 a) 1
  -- (Push p l) >>= f = Push p' l'
  --   where
  --     p' k' = do r <- newRef 0
  --                p $ \i a ->
  --                  do s <- readRef r
  --                     let (Push q m) = (f a)
  --                     q (\j b -> k' (s + j) b)
  --                     writeRef r (s + m)
  --     l' = unsafeInlinePrim $
  --          do r <- newRef 0
  --             p $ \_ a -> 
  --               do let (Push _ l'') = f a
  --                  modifyRef r (+l'')
  --             readRef r
  p >>= f = concat (map f p)
              

-- Same as join 
concat :: (RefMonad m r, PrimMonad m) => Push m (Push m a) -> Push m a
concat (Push p l) = Push q l'
  where
    q k = do r <- newRef 0
             p $ \i a ->
               do s <- readRef r
                  let (Push q' m) = a
                  q' (\j b -> k (s+j) b)
                  writeRef r (s + m)
    l' = unsafeInlinePrim $
         do r <- newRef 0
            p $ \_ a -> 
              do let (Push _ l'') = a
                 modifyRef r (+l'')
            readRef r
           


flatten :: (PrimMonad m, RefMonad m r) => Pull (Push m a) -> Push m a
flatten (Pull ixf n) =
  Push p l
  where
    p = \k ->
          do
          r <- newRef 0 
          forM_ [0..n-1] $ \i -> do
            s <- readRef r
            let (Push p m) = ixf i
            p (\j a -> k (s + j) a) 
            writeRef r (s + m)
    l = sum [len (ixf i) | i <- [0..n-1]] 
        

---------------------------------------------------------------------------
-- Joins
--------------------------------------------------------------------------- 
joinSimple mm = do
  m <- mm
  m 
                            
join :: (PrimMonad m, RefMonad m r)  => Push m (Push m a) -> Push m a
join (Push p n) =
  Push p' l'  
   where
     p' = \k -> do r <- newRef 0
                   p $ \i (Push q m) ->
                     do
                       s <- readRef r
                       q (\j b -> k (s+j) b)
                       writeRef r (s + m) 
     l' = unsafeInlinePrim $
           do r <- newRef 0
              p $ \_ (Push _ l'') -> modifyRef r (+l'')
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

---------------------------------------------------------------------------
-- Scans
---------------------------------------------------------------------------

scanl :: (PullFrom c, RefMonad m r) => (a -> b -> a) -> a -> c b -> Push m a
scanl f init v = Push g n
  where
    (Pull ixf n) = pullfrom v
    g k = do s <- newRef init
             forM_ [0..n-1] $ \ix -> do
               modifyRef s (`f` (ixf ix))
               readRef s >>= k ix

-- Does not work               
scanlPush :: forall m r a b . (RefMonad m r) => (a -> b -> a) -> a -> Push m b -> Push m a 
scanlPush f init (Push pin n) =
  Push p' n
  where
    p' = \k ->
      do
        r <- newRef init
        pin (wf k r)
        
    wf :: RefMonad m r => (Index -> a -> m ()) -> r a -> Index -> b -> m ()
    wf k r = \i b -> 
           do
             v <- readRef r
             let v' = f v b
             writeRef r v'
             k i v'
       
        

foldPush :: forall m r a . (RefMonad m r) => (a -> a -> a) -> a -> Push m a -> m a
foldPush f a (Push p m) =
  do
    r <- newRef a
    p (wf r )
    readRef r
    where
       wf :: RefMonad m r => r a -> Index -> a -> m ()
       wf r = \i b -> 
          do
            v <- readRef r
            let v' = f v b
            writeRef r v'
            -- return ()

-- Same as above but outputs a singleton Push 
foldPushP :: forall m r a . (RefMonad m r) => (a -> a -> a) -> a -> Push m a -> Push m a
foldPushP f a (Push p m) =
  Push p' 1
  where
    p' = \k -> 
      do
        r <- newRef a
        p (wf r )
        v <- readRef r
        k 0 v
              
    wf :: RefMonad m r => r a -> Index -> a -> m ()
    wf r = \i b -> 
           do
             v <- readRef r
             let v' = f v b
             writeRef r v'
             -- return ()



---------------------------------------------------------------------------
-- Conversion Pull Push
---------------------------------------------------------------------------

push (Pull ixf n) =
  Push (\k -> forM_ [0..(n-1)] $ \i ->
         k i (ixf i)) n 

class ToPush m arr where
  toPush ::  arr a -> Push m a

instance ToPush m (Push m) where
  toPush = id

--instance ToPush m Pull where
--  toPush = push 

instance (PullFrom c,Monad m ) => ToPush m c  where
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
     p $ M.write arr
     V.freeze arr 


force :: PrimMonad m => Push m a -> Push m a
force (Push p l) = Push q l
  where
    q k = do
      arr <- M.new l
      p (\i a -> M.write arr i a)
      imm <- V.freeze arr
      let (Pull ixf _) = pullfrom imm
      forM_ [0..l-1] $ \ix ->
        k ix (ixf ix) 

---------------------------------------------------------------------------
-- Conditional Push array 
---------------------------------------------------------------------------

select :: Bool -> Push m a -> Push m a -> Push m a
select b (Push p1 n1) (Push p2 n2)  =
  Push (\k -> if b then p1 k else p2 k) (if b then n1 else n2) 


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
i = pullfrom (P.map (toPush . pullfrom) [[1,2,3],[4,5],[6]])

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
sinput = pullfrom [1..9]

test5 :: Monad m => Pull Int -> Push m Int
test5 arr =  (toPush (pullfrom (P.replicate 45 0))) `before` stride 0 5 arr

test5b :: Monad m => Pull Int -> Push m Int
test5b arr =  (toPush (pullfrom (P.replicate 29 0))) `before` stride 2 3 arr


runTest5 = freeze (test5 sinput :: Push IO Int)
runTest5b = freeze (test5b sinput :: Push IO Int)


---------------------------------------------------------------------------
-- Test Fold
---------------------------------------------------------------------------
i6 :: (RefMonad m r, PrimMonad m) => Push m Int
i6 = (toPush . pullfrom) [1,2,3,4,5,6]

test6 :: (RefMonad m r, PrimMonad m) => Push m Int -> m Int
test6 p = foldPush (+) 0 p 

runTest6 = test6 i6 :: IO Int

---------------------------------------------------------------------------
-- Test scanlPush
---------------------------------------------------------------------------
i7 :: (RefMonad m r, PrimMonad m) => Push m Int
i7 = (toPush . pullfrom) [1,2,3,4,5,6,7,8,9,10]

test7 :: (RefMonad m r, PrimMonad m) => Push m Int -> Push m Int 
test7 p = scanlPush  (+) 0 p 

runTest7 = freeze $ (test7 i7 :: Push IO Int)


---------------------------------------------------------------------------
-- Test unpairP
---------------------------------------------------------------------------
i8 :: (RefMonad m r, PrimMonad m) => Push m (Int,Int)
i8 = (toPush . pullfrom) [(1,2),(3,4),(5,6),(7,8),(9,10)]

test8 :: (RefMonad m r, PrimMonad m) => Push m (Int,Int) -> Push m Int 
test8 p = unpairP  p 

runTest8 = freeze $ (test8 i8 :: Push IO Int)

---------------------------------------------------------------------------
-- Another test of scanlPush
---------------------------------------------------------------------------
i9_1_1,i9_1_2, i9_2_1, i9_2_2,i9_1,i9_2 :: (RefMonad m r, PrimMonad m) => Push m Int
i9_1_1 = (toPush . pullfrom) [1,2,3,4,5] 
i9_1_2 = (toPush . pullfrom) [6,7,8,9,10]
i9_2_1 = (toPush . pullfrom) [1,3,5,7,9] 
i9_2_2 = (toPush . pullfrom) [2,4,6,8,10]
i9_1 = i9_1_1 Push.++ i9_1_2
i9_2 = interleave i9_2_1 i9_2_2

test9 p = scanlPush (+) 0 p

runTest9 = do v1 <- runTest (test9 i9_1)
              v2 <- runTest (test9 i9_2)
              return (v1 == v2)

-- Generic test runner

runTest p = freeze $ (p :: Push IO Int)



---------------------------------------------------------------------------
--
---------------------------------------------------------------------------

input10 = Pull (\i -> i) 5

test10 :: (RefMonad m r, PrimMonad m) => Pull Int -> Push m Int
test10 = repeat . push  

runTest10 = freeze (test10 input10 :: Push IO Int) 


---------------------------------------------------------------------------
-- Simple program
---------------------------------------------------------------------------

input11 = Pull (\i -> i) 16

test11 :: PrimMonad m => Pull Int -> Push m Int
test11 = map (+1) . force . map (+1) . push  

runTest11 = freeze (test11 input11 :: Push IO Int) 
