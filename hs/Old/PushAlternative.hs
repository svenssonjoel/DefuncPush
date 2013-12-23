




{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE ScopedTypeVariables #-} 
{-# LANGUAGE NoMonomorphismRestriction #-} 





module PushAlternative where


import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
import Data.RefMonad

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M 

import Prelude hiding (reverse,scanl,(++),map,exp )
import qualified Prelude as P 

import Data.Supply

-- import Pull

data Pull a = Pull (Index -> a) Length


---------------------------------------------------------------------------
--
---------------------------------------------------------------------------

type Index = Exp Int
type Length = Exp Int 

data Expr = IntVal Int
          | Variable String
          | Add Expr Expr
          | Index String Expr 

newtype Exp a = E (Expr) 

expr :: Exp a -> Expr
expr (E a) = a

exp :: Expr -> Exp a
exp a = E a 



instance  Num (Exp Int) where
  (+) e1 e2 = E $ Add (expr e1) (expr e2) 
  (-) = error "BLAH!" 
  (*) = error "BLOH!"
  abs = undefined 
  signum = undefined 
  fromInteger = E . IntVal . fromInteger



printExp :: Expr -> String
printExp (IntVal a) = show a
printExp (Variable s) = s
printExp (Add e1 e2) = "(" P.++ printExp e1 P.++ " + " P.++ printExp e2 P.++ ")"

instance Show Expr where
  show = printExp 

instance Show (Exp a) where
  show = printExp . expr
---------------------------------------------------------------------------
-- Push array
--------------------------------------------------------------------------- 

data  Push a  = Push (PushT a)  (Prg Length)

---------------------------------------------------------------------------
-- Base language 
---------------------------------------------------------------------------
data Prg a where
  PFor :: String -> Expr -> Prg () -> Prg () -- string is loop variable

  Assign :: String -> Expr -> Expr -> Prg ()

  Allocate :: String -> Expr -> Prg () 
  
  Seq :: Prg a -> (a -> Prg b) -> Prg b
  Ret :: a -> Prg a

  Seq_ :: Prg () -> Prg () -> Prg () 

  Skip :: Prg () 
  
data CMem a = CMem String
data CArray a = CArray String Expr
data CRef a = CRef String 



instance Monad Prg where
  return = Ret 
  (>>=)  = Seq


-- nRef a = do (CArray name)  <- Allocate 1 
--             Assign name 0 a 
--             return (CRef name) 
-- rRef (CRef str) = return (Index str 0)
-- wRef (CRef r) a = Assign r 0 a 
  

printPrg :: Prg a -> (a,String)
printPrg (PFor name n prg) = ((),"for " P.++ name P.++ " in [0.." P.++ show n P.++ "-1]{\n" P.++
                             str P.++
                             "}")
  where
    (b,str) = printPrg prg  
printPrg (Assign name i e) = ((),name P.++"[" P.++ show i P.++"] = " P.++ show e P.++ ";\n")
printPrg (Allocate nom n) = ((), nom P.++ " = allocate(" P.++ show n P.++");\n")
printPrg (ma `Seq` f) = (b, s1 P.++ s2) 
  where
    (a,s1) = printPrg ma
    (b,s2) = printPrg (f a)
printPrg (Ret a) = (a,"RETURN:\n")
                             
instance  Show (Prg a) where
  show = snd . printPrg
---------------------------------------------------------------------------
-- Write Language
---------------------------------------------------------------------------
data Write a  where
  MapW :: Compile b => Write b -> (a -> b) -> Write a           

  ApplyW :: (Index -> a -> Prg ()) -> Write a
  
  VectorW :: Prg Length -> CMem a -> Write a
  AppendW :: Write a -> Index -> Write a


---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------

data PushT b where
  Map      :: Compile a => PushT a -> (a -> b) -> PushT b
  Generate :: Length -> (Index -> b) -> PushT b
  Append   :: Prg Length -> PushT b -> PushT b -> PushT b 



---------------------------------------------------------------------------
-- Library functions
---------------------------------------------------------------------------


push :: Compile a => Pull a -> Push a
push (Pull ixf n) =
  Push (Generate n ixf) (return n) -- Now we require prg is monad 


map :: (Compile b, Compile a) => (a -> b) -> Push a -> Push b
map f (Push p l) = Push (Map p f) l 



(++) :: (Compile a, Num i) => Push a -> Push a -> Push a
(Push p1 l1) ++ (Push p2 l2) =
  Push (Append l1 p1 p2) nl

        where nl = (do l1' <- l1
                       l2' <- l2
                       return $ l1' + l2') 



---------------------------------------------------------------------------
-- Compile 
---------------------------------------------------------------------------

class Compile a where
  mkVar :: Int -> a
  mkArray :: Int -> Expr -> CArray a 
  mkRef   :: Int -> Expr -> CRef a 
  
  injectE :: a -> Expr 
  
  allocate :: CArray a -> Prg () 
  assign   :: CArray a -> Expr -> a -> Prg ()  


instance Compile (Exp a) where
  mkVar i = exp $ Variable $ "v" P.++ show i
  mkArray i n = CArray ("arr" P.++ show i) n 
  mkRef   i e = CRef ("ref" P.++ show i)   -- Cheating and wrong
  
  injectE = expr

  allocate (CArray name n) = Allocate name n
  assign   (CArray name _) i a = Assign name i (injectE a) 


compileW :: Compile a => Supply Int -> PushT a -> Write a -> (CArray a,Prg ())
compileW s p k = undefined 

compile :: Compile a => Supply Int -> PushT a -> Write a -> (CArray a, Prg ())
compile s (Map pt f) k = undefined
      
  

{- 
compileLength :: PushT a -> Write a -> Prg ()
compileLength p (BindLength f r) = undefined 

---------------------------------------------------------------------------
--
---------------------------------------------------------------------------

input1 :: Pull (Exp Int) 
input1 = Pull (\i -> i) (Literal 128)

test1 :: Pull a -> Push a 
test1 =  push  



runTest1 = freeze  (test1 input1 :: Push (Exp Int)) 



test2 ::  Pull a -> Push a
test2 p = p1 ++ p1 
  where
    p1 = push p 

runTest2 = freeze   (test2 input1 :: Push (Exp Int)) 



-} 
