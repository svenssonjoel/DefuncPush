{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}


-- This is the approach described in the paper "Defunctionalizing Push Arrays" 
module CompileNonDefunPush where


import Control.Monad
import Control.Monad.ST

import Control.Monad.Writer
import Control.Monad.State 
import Data.RefMonad

-- replaces the above
import Data.Array.MArray hiding (freeze,Ix,index)
import Data.Array.IO hiding (freeze,Ix,index)
import qualified Data.Array.IO as A 

import Prelude hiding (reverse,scanl,map,read,(++),zipWith)
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
-- Push Array
---------------------------------------------------------------------------
data Push b = Push ((Ix -> b -> CM ()) -> CM ()) Length

len (Push p l) = l 

generate :: Length -> (Ix -> a) -> Push a
generate n ixf = Push p n
   where p k = do for_ n $ \i ->
                    k i (ixf i)

use :: Expable a => CMMem a -> Push a
use mem@(CMMem _ n) = Push p n
  where p k = do for_ n $ \i ->
                   k i (cmIndex mem i) -- a 

map :: Expable a => (a -> b) -> Push a -> Push b
map f (Push p n) = Push p' n
  where p' k = p (\i a -> k i (f a)) 

imap :: Expable a => (Ix -> a -> b) -> Push a -> Push b
imap f (Push p n) = Push p' n
  where p' k = p (\i a -> k i (f i a))

(++) :: Push a -> Push a -> Push a
(++) (Push p1 n1) (Push p2 n2) = Push p n
  where p k = p1 k >> 
              p2 (\i a -> k (n + i) a) 
        n = n1 + n2    

interleave :: Push a -> Push a -> Push a
interleave (Push p1 n1) (Push p2 n2) = Push p n
  where p k = p1 (\i a -> k (2*i) a) >> 
              p2 (\i a -> k (2*i+1) a)
        n = 2 * min_ n1 n2

reverse :: Push a -> Push a
reverse (Push p n) = Push p' n
  where p' k  = p (\i a -> k (n - 1 - i) a)  

rotate :: Length -> Push a -> Push a
rotate l (Push p n) = Push p' n
  where p' k = p (\i a -> k ((i+n) `mod_` n) a)  


force :: Expable a => Push a -> Push a
force (Push p n) = Push p' n
  where p' k = do 
          arr <- allocate n
          p (\i a -> write arr i a) -- VectorW arr)
          for_ n $ \ix ->
             --do a <- read arr ix
                k ix (cmIndex arr ix) -- a 
 
---------------------------------------------------------------------------
-- Conversion Pull Push (Clean this mess up)
---------------------------------------------------------------------------

push (Pull ixf n) =
  generate n ixf

---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: Expable a => Push a -> CompileMonad (CMMem a)
freeze (Push p n)  =
  do arr <- allocate n 
     p $ write arr
     return arr

toVector :: Expable a => Push a -> CompileMonad (CMMem a)
toVector = freeze 

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
--           | Cond Exp Code Code 
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

instance Num (Expr Int)  where
  (+) = inj2 (:+:)
  (-) = inj2 (:-:)
  (*) = inj2 (:*:)
  abs = error "abs: Not implemented"
  signum = error "Signum: Not implemented" 
  fromInteger = inj . Literal . IntVal . fromInteger

instance Num (Expr Float)  where
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

write :: Expable a => CMMem a -> Expr Int -> a -> CM ()
write (CMMem id n) i a = tell $ Write id (toExp i) (toExp a)
             

for_ :: Expable a => Expr Int -> (a -> CM ()) -> CM ()
for_ n f = do i <- newId
              (_,body) <- localCode (f (fromExp (Var i)))
              tell $ For i (unE n) body
par_ n f = do i <- newId
              (_,body) <- localCode (f (fromExp (Var i)))
              tell $ Par i (unE n) body

-- cond :: Expr Bool -> CM () -> CM () -> CM ()
-- cond (E b) p1 p2 = do
--     (_,b1) <- localCode p1
--     (_,b2) <- localCode p2
--     tell $ Cond b b1 b2

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

input = Pull id 16

simple1 :: (Expable a, Num a) => Pull a -> Push a
simple1 = map (+1) . force . push 

compileSimple1 = runCM 0 $ toVector ( simple1 input :: Push (Expr Int))



-- Example without pull arrays entirely
myVec = CMMem "input"  10 

usePrg :: (Expable b,  Num b) => Push b
usePrg = rotate 3 $ reverse $ map (+1) (use myVec)

compileUse = runCM 0 $ toVector (usePrg :: Push (Expr Int))

ex1 :: (Expable b,  Num b) => Push b -> Push b
ex1 = rotate 3 . reverse . map (+1) 
      
compileEx1 = runCM 0 $ toVector ((ex1 arr) :: Push (Expr Int))
  where arr = use myVec


---------------------------------------------------------------------------
-- Touch entire Push API

compileP1 = runCM 0 $
            toVector (generate 10 id) 


compileP2 = runCM 0 $
            toVector (use (CMMem "apa" 10 :: CMMem (Expr Int)))

compileP3 = runCM 0 $
            toVector $
            map (+1) (generate 10 id) 

compileP4 = runCM 0 $
            toVector $
            imap (\i a -> a + i) (generate 10 id)

compileP5 = runCM 0 $
            toVector $
            force (generate 10 id)

compileP6 = runCM 0 $
            toVector $
            (generate 10 id) ++ (generate 10 id)

compileP7 = runCM 0 $
            toVector $
            interleave (generate 10 id) (generate 10 id) 

compileP8 = runCM 0 $
            toVector $
            reverse (generate 10 id)

compileP9 = runCM 0 $
            toVector $
            rotate 4 (generate 10 id) 
            

compileAll = sequence_ $ P.map print
             [compileP1,
              compileP2,
              compileP3,
              compileP4,
              compileP5,
              compileP6,
              compileP7,
              compileP8,
              compileP9]
  where print = putStrLn . show 
                        
