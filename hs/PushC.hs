{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-} 

{-# LANGUAGE ScopedTypeVariables #-}  -- for the bind example only


module PushFS where


import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive

import Control.Monad.Writer
import Control.Monad.State 
import Data.RefMonad

--import qualified Data.Vector as V
--import qualified Data.Vector.Mutable as M 

-- replaces the above
import Data.Array.MArray hiding (freeze)
import Data.Array.IO hiding (freeze)
import qualified Data.Array.IO as A 

import Prelude hiding (reverse,scanl,map)
import qualified Prelude as P 

import GHC.Prim (Constraint) 

---------------------------------------------------------------------------
-- Some basics
---------------------------------------------------------------------------


type Index = Exp
type Length = Int 


---------------------------------------------------------------------------
-- contents of pull
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- Pull array
---------------------------------------------------------------------------

data Pull a = Pull (Index -> a) Length


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
-- Monad with For
---------------------------------------------------------------------------
--class Monad m => ForMonad ctxt m | m -> ctxt where
--  for_ :: (Num a, Enum a, ctxt a) => a -> (a -> m ()) -> m () 

class Monad m => ForMonad ctxt m | m -> ctxt where
  for_ :: ctxt a => a -> (a -> m ()) -> m () 


instance ForMonad Enum IO where
  for_ n f = forM_ [0..(fromEnum n)-1] (f . toEnum)

instance RefMonad m r => MonadRef ctxt m r where
  newRef_ = newRef
  readRef_ = readRef
  writeRef_ = writeRef

---------------------------------------------------------------------------
-- Monad with Memory
---------------------------------------------------------------------------
class Monad m => MemMonad ctxt mem m | m -> mem, m -> ctxt where
  allocate :: Length -> m (mem a)
  write :: (ctxt Index, ctxt a) => mem a -> Index -> a -> m () 

class Empty a
instance Empty a

--instance MemMonad Empty (IOArray Int) IO where
--  allocate n = newArray_ (0,n-1)
--  write = writeArray 


---------------------------------------------------------------------------
-- Push array
--------------------------------------------------------------------------- 
data Push m a = Push (PushT a m)  Length 


---------------------------------------------------------------------------
-- Write Function language
---------------------------------------------------------------------------
data Write a m where
  MapW :: Write b m -> (a -> b) -> Write a m
  IMapW :: Write b m -> (a -> Index -> b) -> Write a m
  IxMapW :: Write a m -> (Index -> Index) -> Write a m 
  ApplyW :: (Index -> a -> m ()) -> Write a m

  UnpairW :: Monad m => Write a m -> Write (a,a) m 

  Evens :: Write a m -> Write a m
  Odds  :: Write a m -> Write a m 
             
  -- Felt awkward when writing this down 
  ZipW  :: Write (a,b) m -> (Index -> b) -> Write a m 

  VectorW :: (ctxt a, ctxt Index,  MemMonad ctxt mem m) => mem a -> Write a m

  AppendW :: Write a m -> Index -> Write a m
  
  -- BindW :: MonadRef ctxt m r =>  (a -> (PushT b m,Length)) -> Write b m -> r Index -> Write a m

  -- BindLength :: MonadRef ctxt m r => (a -> Length) -> r Index -> Write a m

  FoldW :: (MonadRef ctxt m r, ctxt a) => r a -> (a -> a -> a) ->  Write a m
---------------------------------------------------------------------------
-- Apply Write 
---------------------------------------------------------------------------
  
applyW :: Write a m -> (Index -> a -> m ())
applyW (MapW k f) =  \i a -> applyW k i (f a)
applyW (IMapW k f) = \i a -> applyW k i (f a i)
applyW (IxMapW k f) = \i a -> applyW k (f i) a 
applyW (ApplyW k) = k

applyW (UnpairW k) = \i (a,b) ->  applyW k (i*2) a >> applyW k (i*2+1) b

applyW (Evens k) = \i a -> applyW k (i*2) a
applyW (Odds  k) = \i a -> applyW k (1*2+1) a 
                                  
applyW (ZipW k ixf) = \i a -> applyW k i (a, ixf i) 


applyW (VectorW v) = \i a -> write v i a

applyW (AppendW k l) = \i a -> applyW k (l + i) a

-- applyW (BindW f k r) = \i a -> do s <- readRef_ r
--                                   let (q,m) = (f a)
--                                   apply q (AppendW k s)
--                                   writeRef_ r (s + m)

-- applyW (BindLength f r) = \_ a -> do let l'' = f a
--                                      s <- readRef_ r
--                                      writeRef_ r (s + l'') 
--                                      -- modifyRef r (+l'')

applyW (FoldW r f) = \i b -> 
  do
    v <- readRef_ r
    let v' = f v b
    writeRef_ r v'

---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------
data PushT b m  where
  Map  :: PushT a m -> (a -> b) -> PushT b m
  IMap :: PushT a m -> (a -> Index -> b) -> PushT b m
  Append :: Monad m => Index -> PushT b m -> PushT b m -> PushT b m
  Generate :: (ForMonad ctxt m, ctxt Length, ctxt Index)  => (Index -> b) -> Length -> PushT b m
  Iterate :: (ForMonad ctxt m, RefMonad m r, ctxt Length, ctxt Index) => (b -> b) -> b -> Length -> PushT b m
  Unpair :: (ForMonad ctxt m, ctxt Length, ctxt Index) => (Index -> (b,b)) -> Length -> PushT b m
  UnpairP :: Monad m => PushT (b,b) m -> PushT b m 

  Interleave :: Monad m => PushT a m -> PushT a m -> PushT a m 
  
  Zip :: PushT a m -> (Index -> b) -> PushT (a,b) m 
  
  -- Return :: b -> PushT b m
  -- Bind :: (MonadRef ctxt m r, ctxt Index) => PushT a m -> (a -> (PushT b m,Length)) -> PushT b m
  
--   Flatten :: (ForMonad ctxt m, RefMonad m r, ctxt Length) => (Index -> (PushT b m,Length)) -> Length -> PushT b m

  -- Scanl :: (ForMonad ctxt m, RefMonad m r, ctxt Length) => (a -> b -> a) -> a -> (Index -> b) -> Length -> PushT a m 


  Force :: (ForMonad ctxt m, PrimMonad m, ctxt Length) => PushT a m -> Length -> PushT a m 
  
  -- Unsafe

  IxMap :: PushT b m -> (Index -> Index) -> PushT b m
  Seq :: Monad m => PushT b m -> PushT b m -> PushT b m
  Scatter :: (ForMonad ctxt m, ctxt Length, ctxt Index) => (Index -> (b,Index)) -> Length -> PushT b m
  --Stride  :: (ForMonad ctxt m, ctxt Length, ctxt Index) => Index -> Length -> Length -> (Index -> b) -> PushT b m 

---------------------------------------------------------------------------
-- Apply
---------------------------------------------------------------------------
  
apply :: PushT b m -> (Write b m -> m ())
apply (Map p f) = \k -> apply p (MapW k f)
apply (IMap p f) = \k -> apply p (IMapW k f)
apply (IxMap p f) = \k -> apply p (IxMapW k f) 
apply (Append l p1 p2) = \k -> apply p1 k >>
                               apply p2 (AppendW k l)

apply (Generate ixf n) = (\k -> for_ (fromIntegral n) $ \i ->
                           applyW k i (ixf i))
apply (Iterate f a n) = \k ->
  do
    sum <- newRef a 
    for_ (fromIntegral n) $ \i ->
      do
        val <- readRef sum
        applyW k i val 
        writeRef sum (f val) 
        
apply (Unpair f n) = \k -> for_ (fromIntegral n) $ \i ->
                             applyW k (i*2) (fst (f i)) >>
                             applyW k (i*2+1) (snd (f i))
                             
apply (UnpairP p) = \k -> apply p (UnpairW k)

apply (Interleave p q) = \k ->
  do
    apply p (Evens k)
    apply q (Odds  k) 


apply (Zip p ixf) = \k -> let k' = ZipW k ixf
                              in apply p k' 


-- apply (Return a) = \k -> applyW k 0 a
-- apply (Bind p f) = \k -> do r <- newRef_ 0
--                             apply p (BindW f k r)

apply (Seq p1 p2) = \k -> apply p1 k >> apply p2 k
  

apply (Scatter f n) = \k -> for_ (fromIntegral n) $ \i ->
                              applyW k (snd (f i)) (fst (f i))

-- apply (Flatten ixfp n) =
--   \k ->
--           do
--           r <- newRef 0 
--           for_ (fromIntegral n) $ \i -> do
--             s <- readRef r
--             let (p,m) = ixfp i
--             apply p (AppendW k s) 
--             writeRef r (s + m)

-- apply (Scanl f init ixf n) = \k ->
--   do
--     s <- newRef init
--     for_ n $ \ix -> do
--       modifyRef s (`f` (ixf ix))
--       readRef s >>= applyW k ix 


-- apply (Stride start step n f) =
--   \k -> for_ (fromIntegral n) $ \i ->
--          applyW k (start + (fromIntegral step)*i) (f i) 


-- apply (Force p l) =
--   \k -> do arr <- M.new l
--            apply p (VectorW arr) -- (\i a -> M.write arr i a)
--            imm <- V.freeze arr
--            let (Pull ixf _) = pullFrom imm
--            for_ l $ \ix ->
--              applyW k ix (ixf ix) 


---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

len :: Push m a -> Length
len (Push _ n) = n

(<:) :: Push m a -> (Index -> a -> m ()) -> m () 
(Push p _) <: k = apply p (ApplyW k)

-- (<~:) :: Push m a -> Write a m ~> m () 
(Push p _) <~: k = apply p k


map :: (a -> b) -> Push m a -> Push m b
map f (Push p l) = Push (Map p f) l

imap :: (a -> Index -> b) -> Push m a -> Push m b
imap f (Push p l) = Push (IMap p f) l 

ixmap :: (Index -> Index) -> Push m a -> Push m a
ixmap f (Push p l) = Push (IxMap p f) l 

(++) :: Monad m =>  Push m a -> Push m a  -> Push m a
(Push p1 l1) ++ (Push p2 l2) = 
  Push (Append (fromIntegral l1) p1 p2) (l1 + l2) 

reverse :: Push m a -> Push m a
reverse p = ixmap (\i -> (fromIntegral (len p - 1)) - i) p

iterate :: (ForMonad ctxt m, RefMonad m r, ctxt Length, ctxt Index) => Length -> (a -> a) -> a -> Push m a
iterate n f a = Push (Iterate f a n) n 

---------------------------------------------------------------------------
-- unpair / interleave 
--------------------------------------------------------------------------- 
unpair :: (ForMonad ctxt m, ctxt Length, ctxt Index)  => Pull (a,a) -> Push m a
unpair (Pull ixf n) =
  Push (Unpair ixf n) (2*n)

unpairP :: Monad m => Push m (a,a) -> Push m a
unpairP (Push p n) =
  Push (UnpairP p) (2*n)


interleave :: Monad m => Push m a -> Push m a -> Push m a
interleave (Push p m) (Push q n) =
  Push (Interleave p q)  (2 * (min m n))

  
---------------------------------------------------------------------------
-- Zips
--------------------------------------------------------------------------- 
zipPush :: (ForMonad ctxt m, ctxt Length, ctxt Index) => Pull a -> Pull a -> Push m a
zipPush p1 p2 = unpair $  zipPull p1 p2 

zipSpecial :: Monad m => Push m a -> Pull b -> Push m (a,b)
zipSpecial (Push p n1) (Pull ixf n2) =
  Push (Zip p ixf) (min n1 n2)

  
---------------------------------------------------------------------------
--
--------------------------------------------------------------------------- 
scatter :: (ForMonad ctxt m, ctxt Length, ctxt Index)  => Pull (a,Index) -> Push m a
scatter (Pull ixf n) =
  Push (Scatter ixf n) n 

-- combine effects of two push arrays. The second may overwrite the first.
before :: Monad m => Push m a -> Push m a -> Push m a
before (Push p1 n1) (Push p2 n2) =
    Push (Seq p1 p2) (max n1 n2) 


-- flatten :: (ForMonad ctxt m, PrimMonad m, RefMonad m r, ctxt Length) => Pull (Push m a) -> Push m a
-- flatten (Pull ixf n) =
--   Push (Flatten (pFun . ixf) n) l
--   where
--     --p = 
--     l = sum [len (ixf i) | i <- [0..n-1]]
--     pFun (Push p n) = (p,n) 

-- scanl :: (ForMonad ctxt m, PullFrom c, RefMonad m r, ctxt Length) => (a -> b -> a) -> a -> c b -> Push m a
-- scanl f init v = Push (Scanl f init ixf n) n
--   where
--     (Pull ixf n) = pullFrom v


foldPush :: forall ctxt m r a . (MonadRef ctxt m r, ctxt a) => (a -> a -> a) -> a -> Push m a -> m a
foldPush f a (Push p m) = 
  do
    r <- newRef_ a
    apply p (FoldW r f)
    readRef_ r
    

--                   start     step
--stride :: (ForMonad ctxt m, ctxt Length, ctxt Index) => Index -> Length -> Pull a -> Push m a 
--stride start step (Pull ixf n) =
--  Push (Stride start step n ixf) m
--  where m = (start + fromIntegral (n*step)) - 1


--zipByStride :: (ForMonad ctxt m, ctxt Length) => Pull a -> Pull a -> Push m a
--zipByStride p1 p2 = stride 0 2 p1 `before` stride 1 2 p2 

zipByPermute :: Monad m => Push m a -> Push m a -> Push m a
zipByPermute p1 p2 =
   Push (Seq p1' p2') (2*(min (len p1) (len p2))) 
   where
     (Push p1' _) = ixmap (\i -> i*2) p1
     (Push p2' _) = ixmap (\i -> i*2+1) p2 



-- instance (PrimMonad m, RefMonad m r) => Monad (Push m) where
--   return a = Push (Return a) 1
--   (Push p l) >>= f = Push p' l'
--     where
--       -- A trick so that the data types don't depend on the type Push
--       g a = let (Push p l) = f a in (p,l)
--       h a = let (Push _ l) = f a in l
--       p' = Bind p g
--       l' = unsafeInlinePrim $
--            do r <- newRef 0
--               apply p (BindLength h r)
--               readRef r

-- join :: (PrimMonad m, RefMonad m r ) => Push m (Push m a) -> Push m a
-- join mm = do
--   m <- mm
--   m

---------------------------------------------------------------------------
-- Conversion Pull Push (Clean this mess up)
---------------------------------------------------------------------------

push (Pull ixf n) =
  Push (Generate ixf n) n  

class ToPush m arr where
  toPush ::  arr a -> Push m a

instance Monad m => ToPush m (Push m) where
  toPush = id

instance (PullFrom c, ForMonad ctxt m, ctxt Length, ctxt Index) => ToPush m c where
  toPush = push . pullFrom


---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: (ctxt Index, ctxt a, MemMonad ctxt mem m) => Push m a -> m (mem a)
freeze (Push p l) =
  do
     arr <- allocate l
     apply p (VectorW arr)
     return arr
     -- A.freeze arr

toVector :: (ctxt Index, ctxt a, MemMonad ctxt mem m) => Push m a -> m (mem a)
toVector = freeze 

---------------------------------------------------------------------------
-- A defunctionalisable "freeze", called force. 
---------------------------------------------------------------------------
     
--force :: (ForMonad ctxt m, PrimMonad m, ctxt Length) => Push m a -> Push m a
--force (Push p l) = Push (Force p l) l
  
---------------------------------------------------------------------------
-- Simple program
---------------------------------------------------------------------------

input11 = Pull (\i -> i) 16

-- test11 :: (ForMonad ctxt m, PrimMonad m,ctxt Length) => Pull Int -> Push m Int
-- test11 = map (+1) . force . map (+1) . push  

-- test11 :: (ForMonad ctxt m,ctxt Length) => Pull Int -> Push m Int
-- test11 = map (+1)  . map (+1) . push  

-- runTest11 = toVector (test11 input11 :: Push IO Int) 

-- runTest11' = do { s <- runTest11; (getElems s)} 

-- Måste nog vara Exps ?? 
input11' = Pull (\i -> i) 16
test11' :: (ForMonad ctxt m,ctxt Length, ctxt Index) => Pull Exp -> Push m Exp
test11' = map (+1)  . map (+1) . push  

compileTest11 = runCM 0 $ toVector (test11' input11' :: Push CompileMonad Exp) 


---------------------------------------------------------------------------
-- Compile 
---------------------------------------------------------------------------

type Id = String

data Type = Int -- dummy 
            deriving Show 
data Code = Skip
          | Code :>>: Code
          | For Id Exp Code
          | Allocate Id Length Type 
          | Write Id Exp Exp
          | Read Id Exp Id
            deriving Show 

data CodeT a where
  ReturnRef :: CMRef Exp -> CodeT (CMRef a)

instance Monoid Code where
  mempty = Skip
  mappend Skip a = a
  mappend a Skip = a
  mappend a b = a :>>: b 

data Exp = Var Id
         | Literal Int
         | Index Id Exp
         | Exp :+: Exp
         | Exp :-: Exp 
         | Exp :*: Exp 
         deriving Show 

instance Num Exp where
  (+) = (:+:)
  (-) = (:-:)
  (*) = (:*:)
  abs = error "abs: Not implemented"
  signum = error "Signum: Not implemented" 
  fromInteger = Literal . fromInteger

data CMRef a where
  CMRef :: Id -> CMRef a --Exp  

data CMMem a where
  CMMem :: Id -> Length -> CMMem a 

newtype CompileMonad a = CM (StateT Integer (Writer Code) a)
     deriving (Monad, MonadState Integer, MonadWriter Code)


runCM :: Integer -> CompileMonad a -> Code
runCM i (CM s) = snd $ runWriter (evalStateT s i)

localCode :: CompileMonad a -> CompileMonad (a,Code)
localCode (CM m) = do s <- get
                      let ((a,s'),code) = runWriter (runStateT m s)
                      put s
                      return (a,code)

newId :: CompileMonad String 
newId = do i <- get
           put (i + 1)
           return $ "v" P.++ show i 

typeOf :: a -> Type
typeOf _  = Int -- undefined 

instance MonadRef Expable CompileMonad CMRef where
  newRef_ a = do i <- newId
                 tell $ Allocate i 1 (typeOf a)
                 return $ CMRef i 
             
  readRef_ (CMRef i) = do v <- newId 
                          tell $ Read i (Literal 1) v
                          return $ fromExp (Var v)
  writeRef_ (CMRef i) e = tell $ Write i (Literal 1) (toExp e)
  

instance ForMonad Expable CompileMonad where
   for_ n f = do i <- newId
                 (_,body) <- localCode (f (fromExp (Var i)))
                 tell $ For i (toExp n) body

instance MemMonad Expable CMMem CompileMonad where
  allocate n = do
    i <- newId
    tell $ Allocate i n Int -- Cheat!
    return $ CMMem i n
  write (CMMem id n) i a = tell $ Write id (toExp i) (toExp a)  


class Expable a where
  toExp :: a -> Exp
  fromExp :: Exp -> a

instance Expable Exp where
  toExp = id
  fromExp = id

instance Expable Int where
  toExp = Literal
  fromExp (Literal i)  = i --- 
  fromExp e = error $ "Not a Literal: " P.++ show e 

class Monad m => MonadRef ctxt m r | m -> r, m -> ctxt where
  newRef_ :: ctxt a => a -> m (r a)
  readRef_ :: ctxt a => r a -> m a
  writeRef_ :: ctxt a => r a -> a -> m ()
