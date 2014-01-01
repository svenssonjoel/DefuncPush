{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-} 
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-} 
{-# LANGUAGE ScopedTypeVariables #-}



module PushC2 where


import Control.Monad
import Control.Monad.ST

import Control.Monad.Writer
import Control.Monad.State 
import Data.RefMonad

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

type Length = Int 

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
  par_ :: ix -> (ix -> m ()) -> m () 


instance ForMonad Empty Int IO where
   for_ n f = forM_  [0..n-1] (f . toEnum)
   par_ = for_ 

instance RefMonad IO r => MonadRef Empty IO r where
  newRef_ = newRef
  readRef_ = readRef
  writeRef_ = writeRef

---------------------------------------------------------------------------
-- Monad with Memory 
---------------------------------------------------------------------------
class Monad m => MemMonad (ctxt :: * -> Constraint) mem ix a m
  | m -> mem, m -> ctxt where
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
-- Monad with Conditionals 
---------------------------------------------------------------------------
class Monad m => CondMonad b m | m -> b  where
  cond ::  b -> m () -> m () -> m ()
  
instance CondMonad Bool IO where
  cond b e1 e2 = if b then e1 else e2 

---------------------------------------------------------------------------
-- Write Function language
---------------------------------------------------------------------------
data Write m ix a where
  MapW :: Write m ix b -> (a -> b) -> Write m ix a
  ApplyW :: (ix -> a -> m ()) -> Write m ix a
  VectorW :: (ctxt a,  MemMonad ctxt mem ix a m) => mem ix a -> Write m ix a

  IMapW :: Write m ix b -> (a -> ix -> b) -> Write m ix a

  IxMapW :: Write m ix a -> (ix -> ix) -> Write m ix a

  AppendW :: Write m ix a -> ix -> Write m ix a


---------------------------------------------------------------------------
-- Apply Write 
---------------------------------------------------------------------------
  
applyW :: Num ix => Write m ix a -> (ix -> a -> m ())
applyW (MapW k f) =  \i a -> applyW k i (f a)
applyW (ApplyW k) = k
applyW (VectorW v) = \i a -> write v i a

applyW (IMapW k f) = \i a -> applyW k i (f a i)
applyW (IxMapW k f) = \i a -> applyW k (f i) a

applyW (AppendW k l) = \i a -> applyW k (l + i) a

---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------
data PushT m ix b  where
  Map  :: PushT m ix a -> (a -> b) -> PushT m ix b

  -- array creation 
  Generate :: (Num ix, ForMonad ctxt ix m)
              => (ix -> b) -> Length -> PushT m ix b
  Use :: ( Num ix, ctxt b, ForMonad ctxt ix m , MemMonad ctxt mem ix b m) =>
         mem ix b -> Length -> PushT m ix b 

  Force :: (Num ix, ctxt b, MemMonad ctxt mem ix b m, ForMonad ctxt ix m)
           => PushT m ix b -> Length -> PushT m ix b 

  IxMap :: PushT m ix b -> (ix -> ix) -> PushT m ix b
  IMap :: PushT m ix a -> (a -> ix -> b) -> PushT m ix b
  Iterate :: (Num ix, ForMonad ctxt ix m, MonadRef ctxt m r, ctxt Length,ctxt b)
             => (b -> b) -> b -> Length -> PushT m ix b 

  Append :: (Monad m) => ix -> PushT m ix b -> PushT m ix b -> PushT m ix b

-- now PushT can be used as the array type (without any Push Wrapper) 
pushLength :: PushT m ix b -> Length
pushLength (Generate _ l) = l
pushLength (Use _ l) = l
pushLength (Force _ l) = l
pushLength (Iterate _ _ l) = l
pushLength (Map p _ )  = pushLength p
pushLength (IxMap p _) = pushLength p
pushLength (IMap p _)  = pushLength p
pushLength (Append _ p1 p2) = pushLength p1 + pushLength p2

len = pushLength 


---------------------------------------------------------------------------
-- Apply
---------------------------------------------------------------------------
  
apply :: PushT m ix b -> (Write m ix b -> m ())
apply (Map p f) = \k -> apply p (MapW k f)
apply (Generate ixf n) = \k -> par_ (fromIntegral n) $ \i ->
                           applyW k i (ixf i)

apply (Use mem l) = \k -> par_ (fromIntegral l) $ \i ->
                            do a <- read mem i
                               applyW k i a 


apply (IMap p f) = \k -> apply p (IMapW k f)

apply (IxMap p f) = \k -> apply p (IxMapW k f) 

apply (Append l p1 p2) = \k -> apply p1 k >>
                               apply p2 (AppendW k l)


apply (Iterate f a n) = \k ->
  do
    sum <- newRef_ a 
    for_ (fromIntegral n) $ \i ->
      do
        val <- readRef_ sum
        applyW k i val 
        writeRef_ sum (f val) 


apply (Force p l) =
  \k -> do arr <- allocate l
           apply p  (VectorW arr)
           par_ (fromIntegral l) $ \ix ->
             do a <- read arr ix
                applyW k ix a 
        

---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

(<:) :: PushT m ix a -> (ix -> a -> m ()) -> m () 
p <: k = apply p (ApplyW k)

use :: (Num ix, ctxt a, ForMonad ctxt ix m, MemMonad ctxt mem ix a m)
       => mem ix a -> Length -> PushT m ix a
use mem l = Use mem l
-- undefunctionalised 
--  where
--    p k =
--      for_ (fromIntegral l) $ \ix ->
--      do
--        a <- read mem ix
--        k ix a 

map :: (a -> b) -> PushT m ix a -> PushT m ix b
map f p= Map p f

imap :: (a -> ix -> b) -> PushT m ix a -> PushT m ix b
imap f p = IMap p f

ixmap :: (ix -> ix) -> PushT m ix a -> PushT m ix a
ixmap f p = IxMap p f

(++) :: (Num ix, Monad m) =>  PushT m ix a -> PushT m ix a  -> PushT m ix a
p1 ++ p2 = Append (fromIntegral $ len p1) p1 p2  

reverse :: Num ix => PushT m ix a -> PushT m ix a
reverse p = ixmap (\i -> (fromIntegral (len p - 1)) - i) p

iterate :: (Num ix, ForMonad ctxt ix m, MonadRef ctxt m r, ctxt Length, ctxt a)
           => Length -> (a -> a) -> a -> PushT m ix a
iterate n f a = Iterate f a n

---------------------------------------------------------------------------
-- Conversion Pull Push (Clean this mess up)
---------------------------------------------------------------------------

push (Pull ixf n) =
  Generate ixf n

class ToPush m arr where
  toPush ::  arr ix a -> PushT m ix a

instance Monad m => ToPush m (PushT m) where
  toPush = id

---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: (ctxt a, MemMonad ctxt mem ix a m) => PushT m ix a -> m (mem ix a)
freeze p =
  do
     arr <- allocate (len p) 
     apply p (VectorW arr)
     return arr

toVector :: (ctxt a, MemMonad ctxt mem ix a m) => PushT m ix a -> m (mem ix a)
toVector = freeze 

---------------------------------------------------------------------------
-- A defunctionalisable "freeze", called force. 
---------------------------------------------------------------------------
     
force :: (Num ix, ctxt a, MemMonad ctxt mem ix a m, ForMonad ctxt ix m)
         => PushT m ix a -> PushT m ix a
force p = Force p (len p) 

---------------------------------------------------------------------------
-- Simple programs
---------------------------------------------------------------------------
simple1 :: (Num a, Num ix, ForMonad ctxt ix m)
         => Pull ix a -> PushT m ix a
simple1 = map (+1) . push 

compileSimple1 = runCM 0 $ toVector ( simple1 input11 :: PushT CompileMonad (Expr Int) (Expr Int))
runSimple1 = getElems =<< toVector (simple1 input11 :: PushT IO Int Int)


fusion  :: (Num a, Num ix, ForMonad ctxt ix m)
         => Pull ix a -> PushT m ix a
fusion = map (+1) . map (*2) . push 

compileFusion = runCM 0 $ toVector ( fusion input11 :: PushT CompileMonad (Expr Int) (Expr Int))

input11 = Pull id 16
test11 :: (Num a, Num ix,
           ctxt a, MemMonad ctxt mem ix a m,
           ForMonad ctxt ix m)
          => Pull ix a -> PushT m ix a
test11 = map (+1) . force . map (+1) . push  

compileTest11 = runCM 0 $ toVector (test11 input11 :: PushT CompileMonad (Expr Int) (Expr Int))
runTest11 = toVector (test11 input11 :: PushT IO Int Int)

runTest11' = do { s <- runTest11; (getElems s)}


usePrg :: (Num a, Num ix, ctxt a, MemMonad ctxt mem ix a m, ForMonad ctxt ix m)
          => mem ix a -> PushT m ix a 
usePrg input = map (+1) (use input 10 )

compileUsePrg = runCM 0 $ toVector ((usePrg  (CMMem "input1" 10)) :: PushT CompileMonad (Expr Int) (Expr Int))


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
          | Par Id Exp Code -- parallel for loop
          | Allocate Id Length --  Type -- Typecheck instead. 
          | Write Id Exp Exp
          | Read Id Exp Id
          | Cond Exp Code Code 
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
         | Exp :+: Exp
         | Exp :-: Exp
         | Exp :*: Exp
         | Exp :>: Exp
         deriving Show

-- Phantomtypes. 
data Expr a = E {unE :: Exp}


inj  :: Exp -> Expr a
inj e = E e

inj1 :: (Exp -> Exp) -> (Expr a -> Expr b)
inj1 f e = inj $ f (unE e)

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
                 tell $ Allocate i 1 -- (typeOf a)
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
   par_ n f = do i <- newId
                 (_,body) <- localCode (f (fromExp (Var i)))
                 tell $ Par i (toExp n) body


instance MemMonad Expable CMMem (Expr Int) a CompileMonad where
  allocate n = do
    i <- newId
    tell $ Allocate i n -- (typeOf (undefined :: a ))
    return $ CMMem i n
    
  write (CMMem id n) i a = tell $ Write id (toExp i) (toExp a)  
  read (CMMem id n) i = do v <- newId
                           tell $ Read id (toExp i) v
                           return $ fromExp (Var v)
                           
instance CondMonad (Expr Bool) CompileMonad where
  cond (E b) p1 p2 = do
    (_,b1) <- localCode p1
    (_,b2) <- localCode p2
    tell $ Cond b b1 b2
  
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


class Monad m => MonadRef (ctxt :: * -> Constraint)  m r | m -> r, m -> ctxt where
  newRef_ :: ctxt a => a -> m (r a)
  readRef_ :: ctxt a => r a -> m a
  writeRef_ :: ctxt a => r a -> a -> m ()


---------------------------------------------------------------------------
-- Experiments Push a -> Pull a
---------------------------------------------------------------------------

-- # Having indexing and conditionals in the expr type may help.

index_ :: (Monad m, Num ix, Ord ix) => PushT m ix a -> ix -> m a
index_ (Map p f) ix = liftM f (index_ p ix)
index_ (Generate ixf n) ix = return $ ixf ix
index_ (IMap p f) ix = liftM2 f (index_ p ix) (return ix) 
index_ (Iterate f a l) ix =
  do sum <- newRef_ a
     for_ ix $ \i -> 
       do val <- readRef_ sum
          writeRef_ sum (f val)
     readRef_ sum
index_ (Append i p1 p2) ix = if ix < i
                             then index_ p1 ix
                             else index_ p2 (ix - i)
index_ (Use m _) ix = read m ix
index_ (Force p _) ix = index_ p ix
index_ (IxMap p f) ix = index_ p (f ix) -- ?? Not sure I've used 'f' correct

zip :: PushT m ix a -> PushT m ix a -> PushT m ix a

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
-- OLD STUFF
---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------

{- 
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


{-
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



{-
  
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
