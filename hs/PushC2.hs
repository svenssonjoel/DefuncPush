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


module PushC where


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

import Prelude hiding (reverse,scanl,map,read)
import qualified Prelude as P 

import GHC.Prim (Constraint) 

---------------------------------------------------------------------------
-- Some basics
---------------------------------------------------------------------------


type Index = Exp
type Length = Int 


--------------------------------------------------------------------------
-- contents of pull
---------------------------------------------------------------------------

---------------------------------------------------------------------------
-- Pull array
---------------------------------------------------------------------------

data Pull ix a = Pull (ix -> a) Length


zipPull :: Pull i a -> Pull i b -> Pull i (a,b)
zipPull (Pull p1 n1) (Pull p2 n2) = Pull (\i -> (p1 i, p2 i)) (min n1 n2) 

---------------------------------------------------------------------------
-- Convert to Pull array
--------------------------------------------------------------------------- 
class PullFrom c where
  pullFrom :: c i a -> Pull i a

instance PullFrom Pull where
  pullFrom = id 

---------------------------------------------------------------------------
-- Monad with For
---------------------------------------------------------------------------
class Monad m => ForMonad (ctxt :: * -> Constraint) ix m | m -> ctxt where
  for_ :: ix -> (ix -> m ()) -> m () 


instance ForMonad Empty Int IO where
   for_ n f = forM_  [0..n-1] (f . toEnum)

instance RefMonad m r => MonadRef ctxt m r where
  newRef_ = newRef
  readRef_ = readRef
  writeRef_ = writeRef

---------------------------------------------------------------------------
-- Monad with Memory 
---------------------------------------------------------------------------
class Monad m => MemMonad ctxt mem ix a m | m -> mem, m -> ctxt where
  allocate :: ctxt a => Length -> m (mem ix a)
  write :: ctxt a => mem ix a -> ix -> a -> m ()
  read  :: ctxt a => mem ix a -> ix -> m a 

class Empty a
instance Empty a

instance MemMonad Empty IOArray Int a IO where
  allocate n = newArray_ (0,n-1)
  write = writeArray 
  read  = readArray 

---------------------------------------------------------------------------
-- Push array
--------------------------------------------------------------------------- 
data Push m ix a = Push (PushT ix a m)  Length 


---------------------------------------------------------------------------
-- Write Function language
---------------------------------------------------------------------------
data Write ix a m where
  MapW :: Write ix b m -> (a -> b) -> Write ix a m
  ApplyW :: (ix -> a -> m ()) -> Write ix a m
  VectorW :: (ctxt a,  MemMonad ctxt mem ix a m) => mem ix a -> Write ix a m

  IMapW :: Write ix b m -> (a -> ix -> b) -> Write ix a m

  IxMapW :: Write ix a m -> (ix -> ix) -> Write ix a m

  AppendW :: Write ix a m -> ix -> Write ix a m

{-   

  UnpairW :: Monad m => Write a m -> Write (a,a) m 

  Evens :: Write a m -> Write a m
  Odds  :: Write a m -> Write a m 
             
  -- Felt awkward when writing this down 
  ZipW  :: Write (a,b) m -> (Index -> b) -> Write a m 




  
  -- BindW :: MonadRef ctxt m r =>  (a -> (PushT b m,Length)) -> Write b m -> r Index -> Write a m

  -- BindLength :: MonadRef ctxt m r => (a -> Length) -> r Index -> Write a m

  FoldW :: (MonadRef ctxt m r, ctxt a) => r a -> (a -> a -> a) ->  Write a m
-} 
---------------------------------------------------------------------------
-- Apply Write 
---------------------------------------------------------------------------
  
applyW :: Num ix => Write ix a m -> (ix -> a -> m ())
applyW (MapW k f) =  \i a -> applyW k i (f a)
applyW (ApplyW k) = k
applyW (VectorW v) = \i a -> write v i a

applyW (IMapW k f) = \i a -> applyW k i (f a i)
applyW (IxMapW k f) = \i a -> applyW k (f i) a

applyW (AppendW k l) = \i a -> applyW k (l + i) a
{- 


applyW (UnpairW k) = \i (a,b) ->  applyW k (i*2) a >> applyW k (i*2+1) b

applyW (Evens k) = \i a -> applyW k (i*2) a
applyW (Odds  k) = \i a -> applyW k (1*2+1) a 
                                  
applyW (ZipW k ixf) = \i a -> applyW k i (a, ixf i) 






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
-} 
---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------
data PushT ix b m  where
  Map  :: PushT ix a m -> (a -> b) -> PushT ix b m

  -- array creation 
  Generate :: (Num ix, ForMonad ctxt ix m)  => (ix -> b) -> Length -> PushT ix b m
  Use :: (Num ix, ctxt b, ForMonad ctxt ix m , MemMonad ctxt mem ix b m) =>
         mem ix b -> Length -> PushT ix b m 


  
  Force :: (Num ix, ctxt a, MemMonad ctxt mem ix a m, ForMonad ctxt ix m) => PushT ix a m -> Length -> PushT ix a m 

  IxMap :: PushT ix b m -> (ix -> ix) -> PushT ix b m
  IMap :: PushT ix a m -> (a -> ix -> b) -> PushT ix b m

  Append :: Monad m => ix -> PushT ix b m -> PushT ix b m -> PushT ix b m
{-
  Iterate :: (ForMonad ctxt m, RefMonad m r, ctxt Length) => (b -> b) -> b -> Length -> PushT b m
  Unpair :: (ForMonad ctxt m, ctxt Length) => (Index -> (b,b)) -> Length -> PushT b m
  UnpairP :: Monad m => PushT (b,b) m -> PushT b m 

  Interleave :: Monad m => PushT a m -> PushT a m -> PushT a m 
  
  Zip :: PushT a m -> (Index -> b) -> PushT (a,b) m 
  
  -- Return :: b -> PushT b m
  -- Bind :: (MonadRef ctxt m r, ctxt Index) => PushT a m -> (a -> (PushT b m,Length)) -> PushT b m
  
  --Flatten :: (ForMonad ctxt m, RefMonad m r, ctxt Length,ctxt Index) => (Index -> (PushT b m,Length)) -> Length -> PushT b m

  -- Scanl :: (ForMonad ctxt m, RefMonad m r, ctxt Length) => (a -> b -> a) -> a -> (Index -> b) ->7 Length -> PushT a m 


  
  
  -- Unsafe
-}
  
  {-
  Seq :: Monad m => PushT b m -> PushT b m -> PushT b m
  Scatter :: (ForMonad ctxt m, ctxt Length) => (Index -> (b,Index)) -> Length -> PushT b m
  --Stride  :: (ForMonad ctxt m, ctxt Length, ctxt Index) => Index -> Length -> Length -> (Index -> b) -> PushT b m 
-} 
---------------------------------------------------------------------------
-- Apply
---------------------------------------------------------------------------
  
apply :: PushT ix b m -> (Write ix b m -> m ())
apply (Map p f) = \k -> apply p (MapW k f)
apply (Generate ixf n) = \k -> for_ (fromIntegral n) $ \i ->
                           applyW k i (ixf i)

apply (Use mem l) = \k -> for_ (fromIntegral l) $ \i ->
                            do a <- read mem i
                               applyW k i a 


apply (IMap p f) = \k -> apply p (IMapW k f)

apply (IxMap p f) = \k -> apply p (IxMapW k f) 

apply (Append l p1 p2) = \k -> apply p1 k >>
                               apply p2 (AppendW k l)

{-
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
--    \k ->
--         do
--            r <- newRef_ 0 
--            for_ (fromIntegral n) $ \i -> do
--              s <- readRef_ r
--              let (p,m) = ixfp i
--              apply p (AppendW k s) 
--              writeRef_ r (s + (fromIntegral m))


-- apply (Scanl f init ixf n) = \k ->
--   do
--     s <- newRef init
--     for_ n $ \ix -> do
--       modifyRef s (`f` (ixf ix))
--       readRef s >>= applyW k ix 


-- apply (Stride start step n f) =
--   \k -> for_ (fromIntegral n) $ \i ->
--          applyW k (start + (fromIntegral step)*i) (f i) 

-}
apply (Force p l) =
  \k -> do arr <- allocate l
           apply p  (VectorW arr)
           for_ (fromIntegral l) $ \ix ->
             do a <- read arr ix
                applyW k ix a 
        
{-
-- apply (Force p l) =
--   \k -> do arr <- M.new l
--            apply p (VectorW arr) -- (\i a -> M.write arr i a)
--            imm <- V.freeze arr
--            let (Pull ixf _) = pullFrom imm
--            for_ l $ \ix ->
--              applyW k ix (ixf ix) 

-}
---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

len :: Push m ix a -> Length
len (Push _ n) = n

(<:) :: Push m ix a -> (ix -> a -> m ()) -> m () 
(Push p _) <: k = apply p (ApplyW k)

-- (<~:) :: Push m a -> Write a m ~> m () 
(Push p _) <~: k = apply p k

use :: (Num ix, ctxt a, ForMonad ctxt ix m, MemMonad ctxt mem ix a m)
       => mem ix a -> Length -> Push m ix a
use mem l = Push (Use mem l) l

-- undefunctionalised 
--  where
--    p k =
--      for_ (fromIntegral l) $ \ix ->
--      do
--        a <- read mem ix
--        k ix a 


map :: (a -> b) -> Push m ix a -> Push m ix b
map f (Push p l) = Push (Map p f) l
 
imap :: (a -> ix -> b) -> Push m ix a -> Push m ix b
imap f (Push p l) = Push (IMap p f) l 

ixmap :: (ix -> ix) -> Push m ix a -> Push m ix a
ixmap f (Push p l) = Push (IxMap p f) l 

(++) :: (Num ix, Monad m) =>  Push m ix a -> Push m ix a  -> Push m ix a
(Push p1 l1) ++ (Push p2 l2) = 
  Push (Append (fromIntegral l1) p1 p2) (l1 + l2) 

{-
reverse :: Push m a -> Push m a
reverse p = ixmap (\i -> (fromIntegral (len p - 1)) - i) p

iterate :: (ForMonad ctxt m, RefMonad m r, ctxt Length) => Length -> (a -> a) -> a -> Push m a
iterate n f a = Push (Iterate f a n) n 

---------------------------------------------------------------------------
-- unpair / interleave 
--------------------------------------------------------------------------- 
unpair :: (ForMonad ctxt m, ctxt Length)  => Pull (a,a) -> Push m a
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
zipPush :: (ForMonad ctxt m, ctxt Length) => Pull a -> Pull a -> Push m a
zipPush p1 p2 = unpair $  zipPull p1 p2 

zipSpecial :: Monad m => Push m a -> Pull b -> Push m (a,b)
zipSpecial (Push p n1) (Pull ixf n2) =
  Push (Zip p ixf) (min n1 n2)

  
---------------------------------------------------------------------------
--
--------------------------------------------------------------------------- 
scatter :: (ForMonad ctxt m, ctxt Length)  => Pull (a,Index) -> Push m a
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
-} 
---------------------------------------------------------------------------
-- Conversion Pull Push (Clean this mess up)
---------------------------------------------------------------------------

push (Pull ixf n) =
  Push (Generate ixf n) n  

class ToPush m arr where
  toPush ::  arr ix a -> Push m ix a

instance Monad m => ToPush m (Push m) where
  toPush = id

--instance (PullFrom c, ForMonad ctxt m, ctxt Length, ctxt Index) => ToPush m c where
--  toPush = push . pullFrom


---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: (ctxt a, MemMonad ctxt mem ix a m) => Push m ix a -> m (mem ix a)
freeze (Push p l) =
  do
     arr <- allocate l 
     apply p (VectorW arr)
     return arr
     -- A.freeze arr

toVector :: (ctxt a, MemMonad ctxt mem ix a m) => Push m ix a -> m (mem ix a)
toVector = freeze 

---------------------------------------------------------------------------
-- A defunctionalisable "freeze", called force. 
---------------------------------------------------------------------------
     
force :: (Num ix, ctxt a, MemMonad ctxt mem ix a m, ForMonad ctxt ix m) => Push m ix a -> Push m ix a
force (Push p l) = Push (Force p l) l
{-   
---------------------------------------------------------------------------
-- Simple program
---------------------------------------------------------------------------
-}

input11 = Pull (\i -> i) 16
test11 :: (Num a, Num ix,
           ctxt a, MemMonad ctxt mem ix a m,
           ForMonad ctxt ix m)
          => Pull ix a -> Push m ix a
test11 = map (+1) . force . map (+1) . push  

compileTest11 = runCM 0 $ toVector (test11 input11 :: Push CompileMonad (Expr Int) (Expr Int))
runTest11 = toVector (test11 input11 :: Push IO Int Int)

runTest11' = do { s <- runTest11; (getElems s)}


-- Testing use.

--input :: (ctxt ix, Num ix, ForMonad ctxt ix m, MemMonad ctxt mem ix ix m) => m (mem ix ix) 
--input = do arr <- allocate 10
--           for_ (fromIntegral 10) $ \ix ->
--             write arr ix ix
--           return arr

usePrg :: (Num a, Num ix, ctxt a, MemMonad ctxt mem ix a m, ForMonad ctxt ix m)
          => mem ix a -> Push m ix a 
usePrg input = map (+1) (use input 10 )

compileUsePrg = runCM 0 $ toVector ((usePrg  (CMMem "input1" 10)) :: Push CompileMonad (Expr Int) (Expr Int))


---------------------------------------------------------------------------
-- Compile 
---------------------------------------------------------------------------

type Id = String

data Type = Int 
          | Float 
            deriving Show
                     
data Code = Skip
          | Code :>>: Code
          | For Id Exp Code
          | Allocate Id Length Type 
          | Write Id Exp Exp
          | Read Id Exp Id
            deriving Show

instance Monoid Code where
  mempty = Skip
  mappend Skip a = a
  mappend a Skip = a
  mappend a b = a :>>: b 

data Value = IntVal Int
           | FloatVal Float
             deriving Show

data Exp = Var Id
         | Literal Value
         | Index Id Exp
         | Exp :+: Exp
         | Exp :-: Exp
         | Exp :*: Exp
         deriving Show

-- Phantomtypes. 
data Expr a = E {unE :: Exp}


inj  :: Exp -> Expr a
inj e = E e 
inj2 :: (Exp -> Exp -> Exp) -> (Expr a -> Expr b -> Expr c)
inj2 f e1 e2  = inj $ f (unE e1) (unE e2)

instance Num a => Num (Expr Int)  where
  (+) = inj2 (:+:)
  (-) = inj2 (:-:)
  (*) = inj2 (:*:)
  abs = error "abs: Not implemented"
  signum = error "Signum: Not implemented" 
  fromInteger = inj . Literal . IntVal . fromInteger

instance Num a => Num (Expr Float)  where
  (+) = inj2 (:+:)
  (-) = inj2 (:-:)
  (*) = inj2 (:*:)
  abs = error "abs: Not implemented"
  signum = error "Signum: Not implemented" 
  fromInteger = inj . Literal . FloatVal . fromInteger


data CMRef a where
  CMRef :: Id -> CMRef a --Exp  

data CMMem ix a where
  CMMem :: Id -> Length -> CMMem ix a 

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

instance MonadRef Expable CompileMonad CMRef where
  newRef_ a = do i <- newId
                 tell $ Allocate i 1 (typeOf a)
                 tell $ Write i (unE (0 :: Expr Int) ) (toExp a)
                 return $ CMRef i 
             
  readRef_ (CMRef i) = do v <- newId 
                          tell $ Read i (unE (1 :: Expr Int)) v
                          return $ fromExp (Var v)
  writeRef_ (CMRef i) e = tell $ Write i (unE (1 :: Expr Int)) (toExp e)
  

instance ForMonad Expable (Expr Int) CompileMonad where
   for_ n f = do i <- newId
                 (_,body) <- localCode (f (fromExp (Var i)))
                 tell $ For i (toExp n) body

instance MemMonad Expable CMMem (Expr Int) a CompileMonad where
  allocate n = do
    i <- newId
    tell $ Allocate i n (typeOf (undefined :: a ))
    return $ CMMem i n
    
  write (CMMem id n) i a = tell $ Write id (toExp i) (toExp a)  
  read (CMMem id n) i = do v <- newId
                           tell $ Read id (toExp i) v
                           return $ fromExp (Var v) 
      
class Expable a where
  toExp :: a -> Exp
  fromExp :: Exp -> a
  typeOf :: a -> Type 

instance Expable (Expr Int) where
  toExp = unE 
  fromExp = inj 
  typeOf _ = Int

instance Expable (Expr Float) where
  toExp = unE 
  fromExp = inj 
  typeOf _ = Float


class Monad m => MonadRef ctxt m r | m -> r, m -> ctxt where
  newRef_ :: ctxt a => a -> m (r a)
  readRef_ :: ctxt a => r a -> m a
  writeRef_ :: ctxt a => r a -> a -> m ()
