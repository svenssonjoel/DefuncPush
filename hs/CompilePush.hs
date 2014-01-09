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



module CompilePush where


import Control.Monad
import Control.Monad.ST

import Control.Monad.Writer
import Control.Monad.State 
import Data.RefMonad

-- replaces the above
import Data.Array.MArray hiding (freeze,Ix)
import Data.Array.IO hiding (freeze,Ix)
import qualified Data.Array.IO as A 

import Prelude hiding (reverse,scanl,map,read,(++))
import qualified Prelude as P 

import GHC.Prim (Constraint) 

---------------------------------------------------------------------------
-- Some basics
---------------------------------------------------------------------------

type Length = Expr Int
type Ix = Expr Int 


---------------------------------------------------------------------------
-- Pull array
---------------------------------------------------------------------------

data Pull a = Pull (Ix -> a) Length

zipPull :: Pull a -> Pull b -> Pull (a,b)
zipPull (Pull p1 n1) (Pull p2 n2) = Pull (\i -> (p1 i, p2 i)) (min_ n1 n2)

---------------------------------------------------------------------------
-- Convert to Pull array
--------------------------------------------------------------------------- 
class PullFrom c where
  pullFrom :: c a -> Pull a

instance PullFrom Pull where
  pullFrom = id 

---------------------------------------------------------------------------
-- Write Function language
---------------------------------------------------------------------------
data Write a where
  MapW :: Write b -> (a -> b) -> Write a
  ApplyW :: (Ix -> a -> CompileMonad ()) -> Write a
  VectorW :: Expable a => CMMem a -> Write a

  IMapW :: Write b -> (a -> Ix -> b) -> Write a

  IxMapW :: Write a -> (Ix -> CM Ix) -> Write a

  AppendW :: Write a -> Length -> Write a
  
---------------------------------------------------------------------------
-- Apply Write 
---------------------------------------------------------------------------
  
applyW :: Write a -> (Ix -> a -> CompileMonad ())
applyW (MapW k f) =  \i a -> applyW k i (f a)
applyW (ApplyW k) = k
applyW (VectorW v) = \i a -> write v i a

applyW (IMapW k f) = \i a -> applyW k i (f a i)
applyW (IxMapW k f) = \i a -> do ix <- f i
                                 applyW k ix a

applyW (AppendW k l) = \i a -> applyW k (l + i) a
 
---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------
data PushT b  where
  Map  :: (Expable a) => PushT a -> (a -> b) -> PushT b

  -- array creation 
  Generate ::  Expable b => (Ix -> b) -> CM Length -> PushT b
  Use :: Expable b => CMMem b -> CM Length -> PushT b 

  Force :: Expable b =>  PushT b -> CM Length -> PushT b 

  IxMap :: Expable b => PushT b -> (Ix -> CM Ix) -> PushT b
  IMap :: Expable a => PushT a -> (a -> Ix -> b) -> PushT b
  Iterate :: Expable b => (b -> b) -> b -> CM Length -> PushT b 

  Append :: Expable b => CM Length -> PushT b -> PushT b -> PushT b

  Select :: CM (Expr Bool) -> PushT b -> PushT b -> PushT b


data Push a = Push (PushT a) (CompileMonad Length) 

len (Push _ l) =  l 

---------------------------------------------------------------------------
-- Apply
---------------------------------------------------------------------------
  
apply :: Expable b => PushT b -> (Write b -> CompileMonad ())
apply (Map p f) = \k -> apply p (MapW k f)

apply (Generate ixf n) =
  \k -> do l <- n
           par_ l $ \i ->
             applyW k i (ixf i)

apply (Use mem n) =
  \k -> do l <- n
           par_ l $ \i ->
                            do a <- read mem i
                               applyW k i a 


apply (IMap p f) = \k -> apply p (IMapW k f)

apply (IxMap p f) = \k -> apply p (IxMapW k f) 

apply (Append n p1 p2) =
  \k -> do l <- n
           apply p1 k 
           apply p2 (AppendW k l)

apply (Select b p1 p2) = \k ->
  do
    (_,p1') <- localCode $ apply p1 k
    (_,p2') <- localCode $ apply p2 k
    b' <- b
    tell $ Cond (unE b') p1'
                         p2' 

apply (Iterate f a n) = \k -> 
  do
    l <- n
    sum <- newRef_ a 

    for_ l $ \i ->
      do
        val <- readRef_ sum
        applyW k i val 
        writeRef_ sum (f val) 


apply (Force p n) =
  \k -> do l <- n
           arr <- allocate l
           apply p (VectorW arr)
           par_ l $ \ix ->
             do a <- read arr ix
                applyW k ix a 
        
---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------
-- remove ?
--(<:) :: Expable a => PushT a -> (Ix -> a -> CompileMonad ()) -> CompileMonad () 
--p <: k = apply p (ApplyW k)

use :: Expable a => CMMem a -> CM Length -> Push a
use mem l = Push (Use mem l) l 
-- undefunctionalised 
--  where
--    p k =
--      for_ (fromIntegral l) $ \ix ->
--      do
--        a <- read mem ix
--        k ix a 

map :: Expable a => (a -> b) -> Push a -> Push b
map f (Push p l) = Push (Map p f) l 

imap :: Expable a => (a -> Ix -> b) -> Push a -> Push b
imap f (Push p l)  = Push (IMap p f) l 

ixmap :: Expable a => (Ix -> CM Ix) -> Push a -> Push a
ixmap f (Push p l) = Push (IxMap p f) l 


(++) :: Expable a => Push a -> Push a  -> Push a
(Push p1 l1) ++ (Push p2 l2)  = Push (Append l1 p1 p2) (do l1' <- l1
                                                           l2' <- l2
                                                           return $ l1' + l2')

reverse :: Expable a => Push a -> Push a
reverse p = ixmap (\i -> (do n <- len p
                             return $ n - 1 - i))  p

iterate :: Expable a => Length -> (a -> a) -> a -> Push a
iterate n f a = Push (Iterate f a (return n)) (return n) 

---------------------------------------------------------------------------
-- Conversion Pull Push (Clean this mess up)
---------------------------------------------------------------------------

push (Pull ixf n) =
  Push (Generate ixf (return n)) (return n)

---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: (Expable a) => Push a -> CompileMonad (CMMem a)
freeze (Push p l)  =
  do
     n <- l 
     arr <- allocate n 
     apply p (VectorW arr)
     return arr

toVector :: Expable a => Push a -> CompileMonad (CMMem a)
toVector = freeze 

---------------------------------------------------------------------------
-- A defunctionalisable "freeze", called force. 
---------------------------------------------------------------------------
     
force :: Expable a => Push a -> Push a
force (Push p l)  = Push (Force p l) l  

---------------------------------------------------------------------------
-- Conditional Push array ? 
---------------------------------------------------------------------------
select :: CM (Expr Bool) -> Push a -> Push a -> Push a
--select b (Push p1 n1) (Push p2 n2)  =
--  Push (\k -> if b then p1 k else p2 k) (if b then n1 else n2)
select b (Push p1 l1) (Push p2 l2) =
  Push (Select b p1 p2) (do n1 <- l1
                            n2 <- l2
                            r <- newRef_ n1
                            b' <- b
                            cond b' (return ())
                                   (writeRef_ r n2)
                            readRef_ r) 


---------------------------------------------------------------------------
-- Simple programs
---------------------------------------------------------------------------

input11 = Pull id 16

simple1 :: (Expable a, Num a) => Pull a -> Push a
simple1 = map (+1) . force . push 

compileSimple1 = runCM 0 $ toVector ( simple1 input11 :: Push (Expr Int))
-- runSimple1 = getElems =<< toVector (simple1 input11 :: PushT IO Int Int)

--compileSimple1' = runCM 0 $ toVector $ takeSome (simple1 input11 :: PushT (Expr Int)) 10

simple2 :: (Expable a, Num a) => Pull a -> Push a
simple2 arr = a1 ++ a2 
  where
    a1 = push arr
    a2 = push arr


compileSimple2 = runCM 0 $ toVector ( simple2 input11 :: Push (Expr Int))
-- runSimple1 = getElems =<< toVector (simple1 input11 :: PushT IO Int Int)

compileSimple2' = runCM 0 $ toVector $ takeSome (simple2 input11 :: Push (Expr Int)) (return (fromIntegral 10))

{-
-- Simple2
Allocate "v0" (E {unE = Literal (IntVal 16) :+: Literal (IntVal 16)}) :>>:
  (Par "v1" (Literal (IntVal 16)) (Write "v0" (Var "v1") (Var "v1")) :>>:
   Par "v2" (Literal (IntVal 16)) (Write "v0" (Literal (IntVal 16) :+: Var "v2") (Var "v2")))

--Simple2'
Allocate "v0" (E {unE = Literal (IntVal 10)}) :>>:
  Cond (LEq (Literal (IntVal 10)) (Literal (IntVal 16)))
    (Par "v1" (Literal (IntVal 10))
      (Write "v0" (Var "v1") (Var "v1")))
    (Par "v1" (Literal (IntVal 10))
       (Write "v0" (Var "v1") (Var "v1")) :>>:
     Par "v2" (Literal (IntVal 10) :-: Literal (IntVal 16))
       (Write "v0" (Literal (IntVal 16) :+: Var "v2") (Var "v2")))
-}

{- 
fusion  :: (Num a, Num ix, ForMonad ctxt ix m)
         => Pull ix a -> PushT m ix a
fusion = map (+1) . map (*2) . push 

compileFusion = runCM 0 $ toVector ( fusion input11 :: PushT CompileMonad (Expr Int) (Expr Int))


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

-}

-- Maybe this program should be possible?

{- 
monadic1 :: (Num ix, ctxt a, ForMonad ctxt ix m, MemMonad ctxt mem ix ix m)
            => Pull ix ix => m (PushT m ix ix) 
monadic1 arr =
  do mem <- freeze $ push arr
     a   <- read mem 3 
     let arr1 = Pull (\i -> i) a -- impossible
     push arr1    
-} 
  

---------------------------------------------------------------------------
-- Things that are hard to do with Push or Pull Arrays, but now "simple"
---------------------------------------------------------------------------
--divConc :: PushT m ix a -> (PushT m ix a -> PushT m ix a -> PushT m ix b) -> PushT m ix b
--divConc (Generate ixf n) f | n > 1 = divConc (Generate ixf (n `div` 2))

-- Transform a program that computes a Push array
-- to a program that computes a single element.

index :: Expable a => Push a -> Ix -> CompileMonad a
index (Push p n) ix = indexP p ix 
  
indexP :: Expable a => PushT a -> CM Ix -> CompileMonad a
indexP (Map p f) ix        = liftM f (indexP p ix)
indexP (Generate ixf n) ix = liftM ixf ix

indexP (Use mem l) ix      = do i <- ix
                                read mem i

indexP (IMap p f)  ix      = do i <- ix
                                liftM (\a -> f a i) (indexP p ix)

indexP (Force p l) ix      = indexP p ix

indexP (IxMap p f) ix      = do i <- ix
                                indexP p (f i)

indexP (Iterate f a l) ix  =
  do sum <- newRef_ a
     ix' <- ix
     for_ ix' $ \(i :: Expr Int) -> 
         do val <- readRef_ sum
            writeRef_ sum (f val)
     readRef_ sum
 
-- need conditionals in language. 
indexP (Append l p1 p2) ix = do
  r <- mkRef_
  ix' <- ix
  l' <- l
  cond (ix' >* l')
       (do a <- indexP p2 (return $ ix' - l')
           writeRef_ r a)
       (do a <- indexP p1 (return $ ix') 
           writeRef_ r a)
  readRef_ r


takeSome :: Expable a => Push a -> CM Length -> Push a
takeSome (Push p l) m = Push (takeSome' p m) m

takeSome' :: Expable a => PushT a -> CM Length -> PushT a 
takeSome' (Map p f) m = Map (takeSome' p m) f 
takeSome' (Generate ixf n) m = Generate ixf m --conditionals !
takeSome' (Use mem l) m = Use mem m -- conditionals !
takeSome' (IMap p f) m = IMap (takeSome' p m) f
takeSome' (Force p l) m = Force (takeSome' p m) m -- conditionals !
takeSome' (IxMap p f) m = IxMap (takeSome' p m) f
takeSome' (Iterate f a l) m = Iterate f a m -- conditionals !
takeSome' (Append l p1 p2) m =  
  Select (do m' <- m
             l' <- l
             return $ m' <=* l')
         (takeSome' p1 m)
         (Append l (takeSome' p1 m) (takeSome' p2 (do m' <- m
                                                      l' <- l
                                                      return $ m'-l')))



  
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
         | Gt  Exp Exp
         | LEq Exp Exp 
         | Min Exp Exp 
         deriving Show

-- Phantomtypes. 
data Expr a = E {unE :: Exp}
  deriving Show 

(>*) :: Expr a -> Expr a -> Expr Bool
(>*) = inj2 Gt

(<=*) :: Expr a -> Expr a -> Expr Bool
(<=*) = inj2 LEq

min_ :: Expr a -> Expr a -> Expr a
min_ = inj2 Min

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

data CMMem a where
  CMMem :: Id -> Length -> CMMem a 

newtype CompileMonad a = CM (StateT Integer (Writer Code) a)
     deriving (Monad, MonadState Integer, MonadWriter Code)

type CM = CompileMonad


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

allocate n = do
    i <- newId
    tell $ Allocate i n -- (typeOf (undefined :: a ))
    return $ CMMem i n
    
write (CMMem id n) i a = tell $ Write id (toExp i) (toExp a)  
read (CMMem id n) i = do v <- newId
                         tell $ Read id (toExp i) v
                         return $ fromExp (Var v)

newRef_ a = do i <- newId
               tell $ Allocate i 1 -- (typeOf a)
               tell $ Write i (unE (0 :: Expr Int) ) (toExp a)
               return $ CMRef i
mkRef_ = do i <- newId
            tell $ Allocate i 1 -- (typeOf (undefined :: a))
            return $ CMRef i
             
readRef_ (CMRef i) = do v <- newId 
                        tell $ Read i (unE (1 :: Expr Int)) v
                        return $ fromExp (Var v)
writeRef_ (CMRef i) e = tell $ Write i (unE (1 :: Expr Int)) (toExp e)

for_ :: Expable a1 => Expr Int -> (a1 -> CompileMonad ()) -> CompileMonad ()
for_ n f = do i <- newId
              (_,body) <- localCode (f (fromExp (Var i)))
              tell $ For i (unE n) body
par_ n f = do i <- newId
              (_,body) <- localCode (f (fromExp (Var i)))
              tell $ Par i (unE n) body


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

