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
import Data.Array.MArray hiding (freeze,Ix,index)
import Data.Array.IO hiding (freeze,Ix,index)
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

takePull :: Length -> Pull a -> Pull a
takePull n (Pull ixf l) = Pull ixf n

dropPull :: Length -> Pull a -> Pull a
dropPull n (Pull ixf l) = Pull (\i -> ixf (i+n)) (l - n)

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
-- data Write a where
--   MapW ::  (a -> b) -> Write b -> Write a
--   ApplyW :: (Ix -> a -> CompileMonad ()) -> Write a
--   VectorW :: Expable a => CMMem a -> Write a

--   IMapW :: (Ix -> a -> b) -> Write b -> Write a

-- --   IxMapW :: Write a -> (Ix -> Ix) -> Write a

--   AppendW :: Length -> Write a -> Write a

--   EvensW :: Write a -> Write a
--   OddsW  :: Write a -> Write a

--   ReverseW :: Length -> Write a -> Write a
--   RotateW  :: Length -> Length -> Write a -> Write a
  
  
---------------------------------------------------------------------------
-- Apply Write 
---------------------------------------------------------------------------
  
-- applyW :: Write a -> (Ix -> a -> CompileMonad ())
-- applyW (MapW f k) =  \i a -> applyW k i (f a)
-- applyW (ApplyW k) = k
-- applyW (VectorW v) = \i a -> write v i a

-- applyW (IMapW f k) = \i a -> applyW k i (f i a)
-- -- applyW (IxMapW k f) = \i a -> applyW k (f i) a

-- applyW (AppendW l k) = \i a -> applyW k (l + i) a

-- applyW (EvensW k) = \i a -> applyW k (2*i) a
-- applyW (OddsW k)  = \i a -> applyW k (2*i+1) a 

-- applyW (ReverseW l k) = \i a -> applyW k (l - 1 - i) a
-- applyW (RotateW l n k) = \i a -> applyW k ((i + n) `mod_` l) a

---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------
data PushT b where
  Map  :: (Expable a) => (a -> b) -> PushT a -> PushT b

  -- array creation 
  Generate ::  Expable b => Length -> (Ix -> b) -> PushT b
  Use :: Expable b => Length -> CMMem b -> PushT b 

  Force :: Expable b =>  Length -> PushT b -> PushT b 

-- IxMap :: Expable b => PushT b -> (Ix -> Ix) -> PushT b
  IMap :: Expable a => (Ix -> a -> b) -> PushT a -> PushT b
--  Iterate :: Expable b => Length -> (b -> b) -> b -> PushT b 

  Append :: Expable b => Length -> PushT b -> PushT b -> PushT b

--  Select :: Expr Bool -> PushT b -> PushT b -> PushT b
  -- pushLength on Select, requires evaluation of an Expr.

  Interleave :: PushT b -> PushT b -> PushT b  

  -- Permutations
  Reverse :: PushT b -> PushT b
  Rotate  :: Length -> PushT b -> PushT b 
  

  
-- now PushT can be used as the array type (without any Push Wrapper) 
pushLength :: PushT b -> Length
pushLength (Generate l _) = l
pushLength (Use l _) = l
pushLength (Force l _) = l
-- pushLength (Iterate l _ _ ) = l
pushLength (Map _ p)  = pushLength p
-- pushLength (IxMap p _) = pushLength p
pushLength (IMap _ p)  = pushLength p
pushLength (Append _ p1 p2) = pushLength p1 + pushLength p2
--pushLength (Interleave p1 p2) = 2 * (min (pushLength p1) (pushLength p2))
pushLength (Interleave p1 p2) = 2 * (min_ (pushLength p1) (pushLength p2))

pushLength (Reverse p) = pushLength p
pushLength (Rotate _ p) = pushLength p

len = pushLength 
---------------------------------------------------------------------------
-- Apply
---------------------------------------------------------------------------
  
apply :: Expable b => PushT b -> ((Ix -> b -> CM ()) -> CM ())
apply (Generate n ixf) =
  \k -> do for_ n $ \i ->
             k i (ixf i)

apply (Use n mem) =
  \k -> do for_ n $ \i ->
             do a <- read mem i
                k i a 

apply (Map f p) =
  \k -> apply p (\i a -> k i (f a)) 

apply (IMap f p) =
  \k -> apply p (\i a -> k i (f i a))


apply (Append n p1 p2) =
  \k -> apply p1 k >> 
        apply p2 (\i a -> k (n + i) a) 
           
apply (Interleave p1 p2) =
  \k -> apply p1 (\i a -> k (2*i) a) >> 
        apply p2 (\i a -> k (2*i+1) a)  

apply (Reverse p) =
  \k -> apply p (\i a -> k ((len p) - 1 - i) a) 
apply (Rotate n p) =
  \k -> apply p (\i a -> k ((i+n) `mod_` (len p)) a) 






apply (Force n p) =
  \k -> do -- l <- n
           arr <- allocate n
           apply p (\i a -> write arr i a) -- VectorW arr)
           par_ n $ \ix ->
             do a <- read arr ix
                k ix a 



---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------
-- remove ?
--(<:) :: Expable a => PushT a -> (Ix -> a -> CompileMonad ()) -> CompileMonad () 
--p <: k = apply p (ApplyW k)

use :: Expable a => Length -> CMMem a -> PushT a
use l mem = Use l mem
-- undefunctionalised 
--  where
--    p k =
--      for_ (fromIntegral l) $ \ix ->
--      do
--        a <- read mem ix
--        k ix a 

map :: Expable a => (a -> b) -> PushT a -> PushT b
map f p = Map f p

imap :: Expable a => (Ix -> a -> b) -> PushT a -> PushT b
imap f p  = IMap f p 

-- ixmap :: Expable a => (Ix -> Ix) -> Push a -> Push a
-- ixmap f (Push p l) = Push (IxMap p f) l 


(++) :: Expable a => PushT a -> PushT a -> PushT a
p1 ++ p2 = Append l1 p1 p2
  where
    l1 = len p1

--reverse :: Expable a => Push a -> Push a
--reverse p = ixmap (\i -> (len p - 1 - i))  p

--iterate :: Expable a => Length -> (a -> a) -> a -> PushT a
--iterate n f a = Iterate n f a

interleave :: Monad m => PushT a -> PushT a -> PushT a
interleave p1 p2 = Interleave p1 p2 

reverse :: PushT a -> PushT a
reverse p = Reverse p 

rotate :: Length -> PushT a -> PushT a
rotate n p = Rotate n p 
---------------------------------------------------------------------------
-- Conversion Pull Push (Clean this mess up)
---------------------------------------------------------------------------

push (Pull ixf n) =
  Generate n ixf

---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: (Expable a) => PushT a -> CompileMonad (CMMem a)
freeze p  =
  do
     arr <- allocate (len p)
     apply p (\i a -> write arr i a)  
     return arr

toVector :: Expable a => PushT a -> CompileMonad (CMMem a)
toVector = freeze 

---------------------------------------------------------------------------
-- A defunctionalisable "freeze", called force. 
---------------------------------------------------------------------------
     
force :: Expable a => PushT a -> PushT a
force p = Force (len p) p 

---------------------------------------------------------------------------
-- Conditional Push array ? 
---------------------------------------------------------------------------
--select :: Expr Bool -> Push a -> Push a -> Push a
--select b (Push p1 n1) (Push p2 n2)  =
--  Push (\k -> if b then p1 k else p2 k) (if b then n1 else n2)
--select b (Push p1 l1) (Push p2 l2) =
--  Push (Select b p1 p2) (ifThenElse b l1 l2) -- undefined -- do n1 <- l1
                            -- n2 <- l2
                            -- r <- newRef_ n1
                            -- b' <- b
                            -- cond b (return ())
                            --        (writeRef_ r n2)
                            -- readRef_ r) 


---------------------------------------------------------------------------
-- Simple programs
---------------------------------------------------------------------------

-- input11 = Pull id 16

-- simple1 :: (Expable a, Num a) => Pull a -> PushT a
-- simple1 = map (+1) . force . push 

-- compileSimple1 = runCM 0 $ toVector ( simple1 input11 :: PushT (Expr Int))
-- -- runSimple1 = getElems =<< toVector (simple1 input11 :: PushT IO Int Int)

-- --compileSimple1' = runCM 0 $ toVector $ takeSome (simple1 input11 :: PushT (Expr Int)) 10

-- simple2 :: (Expable a, Num a) => Pull a -> PushT a
-- simple2 arr = a1 ++ a2 
--   where
--     a1 = push arr
--     a2 = push arr


-- compileSimple2 = runCM 0 $ toVector ( simple2 input11 :: PushT (Expr Int))
-- runSimple1 = getElems =<< toVector (simple1 input11 :: PushT IO Int Int)

--compileSimple2' = runCM 0 $ toVector $ takeSome (simple2 input11 :: PushT (Expr Int)) (fromIntegral 10)
  
---------------------------------------------------------------------------
-- Things that are hard to do with Push or Pull Arrays, but now "simple"
---------------------------------------------------------------------------

-- Transform a program that computes a Push array
-- to a program that computes a single element.

-- TODO: Remove iterate from the language.

-- index :: Expable a => PushT a -> Ix -> CompileMonad a
-- index (Map f p) ix        = liftM f (index p ix)
-- index (Generate n ixf) ix = return $ ixf ix

-- index (Use l mem) ix      = return $ cmIndex mem ix -- read mem ix

-- index (IMap f p)  ix      = liftM (\a -> f ix a) (index p ix)

-- index (Force l p) ix      = index p ix

-- index (Append l p1 p2) ix = do
--   a <- index p2 (ix - l)
--   b <- index p1 ix
--   return $ ifThenElse1 (ix >* l) a b 

-- index (Interleave p1 p2) ix = do
--   a <- index p1 (ix `div_` 2)
--   b <- index p2 (ix `div_` 2)
--   return $ ifThenElse1 (ix `mod_` 2 ==* 0) a b

-- index (Reverse p) ix = index p (len p - 1 - ix)
-- index (Rotate dist p) ix = index p ((ix - dist) `mod_` (len p)) 

index :: Expable a => PushT a -> Ix -> a
index (Map f p) ix        = f (index p ix)
index (Generate n ixf) ix = ixf ix

index (Use l mem) ix      = cmIndex mem ix -- read mem ix

index (IMap f p)  ix      = f ix (index p ix)

index (Force l p) ix      = index p ix

index (Append l p1 p2) ix =
  ifThenElse1 (ix >* l)  
    (index p2 (ix - l))
    (index p1 ix)

index (Interleave p1 p2) ix =
  ifThenElse1 (ix `mod_` 2 ==* 0) 
    (index p1 (ix `div_` 2))
    (index p2 (ix `div_` 2))

index (Reverse p) ix = index p (len p - 1 - ix)
index (Rotate dist p) ix = index p ((ix - dist) `mod_` (len p)) 


-- takesome requires some kind of conditional push array.  
-- Select.
--  
  
-- takeSome :: Expable a => Push a -> Length -> Push a
-- takeSome (Push p l) m = Push (takeSome' p m) m

-- takeSome' :: Expable a => PushT a -> Length -> PushT a 
-- takeSome' (Map p f) m = Map (takeSome' p m) f 
-- takeSome' (Generate ixf n) m = Generate ixf m --conditionals !
-- takeSome' (Use mem l) m = Use mem m -- conditionals !
-- takeSome' (IMap p f) m = IMap (takeSome' p m) f
-- takeSome' (Force p l) m = Force (takeSome' p m) m -- conditionals !
-- takeSome' (IxMap p f) m = IxMap (takeSome' p m) f
-- takeSome' (Iterate f a l) m = Iterate f a m -- conditionals !
-- takeSome' (Append l p1 p2) m =  
--   Select (m <=* l)
--          (takeSome' p1 m)
--          (Append l (takeSome' p1 m) (takeSome' p2 (m-l)))

---------------------------------------------------------------------------
-- Push to Pull
---------------------------------------------------------------------------

convert :: Expable a => PushT a -> Pull a
convert p = Pull (\ix -> index p ix) (len p) 


  
---------------------------------------------------------------------------
-- Compile 
---------------------------------------------------------------------------

type Id = String

data Type = Int 
          | Float
          | Bool
            deriving Show
                     
data Code = Skip
          | Code :>>: Code
          | For Id Exp Code
          | Par Id Exp Code 
          | Allocate Id Length 
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
           | BoolVal  Bool

instance Show Value where
  show (IntVal i) = show i
  show (FloatVal f) = show f
  show (BoolVal b) = show b 

data Exp = Var Id
         | Literal Value
         | Index String Exp 
         | Exp :+: Exp
         | Exp :-: Exp
         | Exp :*: Exp
         | Mod Exp Exp
         | Div Exp Exp
         | Eq  Exp Exp 
         | Gt  Exp Exp
         | LEq Exp Exp 
         | Min Exp Exp
         | IfThenElse Exp Exp Exp
           
instance Show Exp where
  show (Var id) = id
  show (Literal v) = show v
  show (Index str e) = str P.++ "[" P.++ show e P.++ "]" 
  show (a :+: b) = parens $ show a P.++ " + " P.++ show b
  show (a :-: b) = parens $ show a P.++ " - " P.++ show b
  show (a :*: b) = parens $ show a P.++ " * " P.++ show b
  show (Mod a b) = parens $ show a P.++ " % " P.++ show b
  show (Div a b) = parens $ show a P.++ " / " P.++ show b
  show (Eq a b) = parens $ show a P.++ " == " P.++ show b
  show (Gt a b) = parens $ show a P.++ " > " P.++ show b
  show (LEq a b) = parens $ show a P.++ " <= " P.++ show b
  show (Min a b) = parens $ "min" P.++ show a P.++ show b
  show (IfThenElse b e1 e2) = parens $ show b P.++ " ? " P.++ show e1 P.++ " : " P.++ show e2
  
  

parens str = "(" P.++ str P.++ ")" 


-- Phantomtypes. 
data Expr a = E {unE :: Exp}
instance Show (Expr a) where
  show = show . unE 


ifThenElse :: Expr Bool -> Expr a -> Expr a -> Expr a
ifThenElse b e1 e2 = E $ IfThenElse (unE b) (unE e1) (unE e2) 

ifThenElse1 :: Expable a =>  Expr Bool -> a -> a -> a
ifThenElse1 b e1 e2 = fromExp $ IfThenElse (unE b) (toExp e1) (toExp e2) 

cmIndex :: Expable a => CMMem a -> Ix -> a
cmIndex (CMMem nom n) ix = fromExp $ Index nom (toExp ix)

mod_ :: Expr Int -> Expr Int -> Expr Int
mod_ = inj2 Mod

div_ :: Expr Int -> Expr Int -> Expr Int
div_ = inj2 Div
--minE :: Expr Int -> Expr Int -> Expr Int
--minE = inj2 Min

(==*) :: Expr a -> Expr a -> Expr Bool
(==*) = inj2 Eq 

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

instance Expable (Expr Bool) where
  toExp = unE
  fromExp = inj
  typeOf _ = Bool

instance Expable (Expr Int) where
  toExp = unE 
  fromExp = inj 
  typeOf _ = Int

instance Expable (Expr Float) where
  toExp = unE 
  fromExp = inj 
  typeOf _ = Float











---------------------------------------------------------------------------
-- Simple programs
---------------------------------------------------------------------------

input1 = Pull id 16

simple1 :: (Expable a, Num a) => Pull a -> PushT a
simple1 = map (+1) . force . push 

compileSimple1 = runCM 0 $ toVector ( simple1 input1 :: PushT (Expr Int))



-- Example without pull arrays entirely
myVec = CMMem "input"  10 

usePrg :: (Expable b,  Num b) => PushT b
usePrg = rotate 3 $ reverse $ map (+1) (use 10 myVec )

compileUse = runCM 0 $ toVector (usePrg :: PushT (Expr Int))

ex1 :: (Expable b,  Num b) => PushT b
ex1 = rotate 3 $ reverse $ map (+1) (use 10 myVec )
 
compileEx1 = runCM 0 $ toVector (ex1 :: PushT (Expr Int))
--runUse :: IO (V.Vector Int)
--runUse = toVector (usePrg :: PushT IO Int) 


-- -- zipP test
-- prg :: (Enum a, Enum b, Num a, Num b, PrimMonad m) => PushT m (a, b)
-- prg = zipP (use 10 myVec) (use 10 myVec)

-- runPrg :: IO (V.Vector (Int, Int))
-- runPrg = toVector (prg :: PushT IO (Int,Int))





---------------------------------------------------------------------------
{-
Allocate "v0" (E {unE = Literal (IntVal 10)}) :>>:
For "v1" (Literal (IntVal 10))
  (Read "inputArray" (Var "v1") "v2" :>>:
   Write "v0" (Mod (((Literal (IntVal 10) :-:
                      Literal (IntVal 1)) :-: Var "v1") :+:
Literal (IntVal 3)) (Literal (IntVal 10))) (Var "v2" :+: Literal (IntVal 1)))
-} 
