




{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE ScopedTypeVariables #-} 
{-# LANGUAGE NoMonomorphismRestriction #-} 

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}

module PushAlternative where


import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
import Data.RefMonad

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M 

import Prelude hiding (reverse,scanl,(++))
import qualified Prelude as P 

-- import Pull

data Pull i a = Pull (i -> a) i


---------------------------------------------------------------------------
--
---------------------------------------------------------------------------

type Index = Exp Int
type Length = Exp Int 

data Exp a where
   Literal :: Show a => a -> Exp a 
   Variable :: String -> Exp a

   Add :: Exp a -> Exp a -> Exp a 
   
   Index :: String -> Index -> Exp a 

instance (Show a, Num a) => Num (Exp a) where
  (+) = Add
  (-) = error "BLAH!" 
  (*) = error "BLOH!"
  abs = undefined 
  signum = undefined 
  fromInteger = Literal . fromInteger

printExp :: Exp a -> String
printExp (Literal a) = show a
printExp (Variable s) = s
printExp (Add e1 e2) = "(" P.++ printExp e1 P.++ " + " P.++ printExp e2 P.++ ")"

instance Show (Exp a) where
  show = printExp 
---------------------------------------------------------------------------
-- Push array
--------------------------------------------------------------------------- 

data  Push ctx i a  = Push (PushT ctx i a)  i

---------------------------------------------------------------------------
-- Base language 
---------------------------------------------------------------------------
data Prg a where
  PFor :: String -> Length -> Prg () -> Prg () -- string is loop variable

  Assign :: String -> Index -> Exp a -> Prg ()

  Allocate :: Length -> Prg String
  Seq :: Prg a -> (a -> Prg b) -> Prg b
  Ret :: a -> Prg a

instance Monad Prg where
  return = Ret 
  (>>=)  = Seq

printPrg :: Prg a -> (a,String)
printPrg (PFor name n prg) = ((),"for " P.++ name P.++ " in [0.." P.++ show n P.++ "-1]{\n" P.++
                             str P.++
                             "}")
  where
    (b,str) = printPrg prg  
printPrg (Assign name i e) = ((),name P.++"[" P.++ show i P.++"] = " P.++ show e P.++ ";\n")
printPrg (Allocate n) = ("fresh", "fresh = allocate(" P.++ show n P.++");\n")
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
data Write ctx mem (ref :: * -> *)  i a prg where
  MapW ::  ctx b => Write ctx mem ref i b prg -> (a -> b) -> Write ctx mem ref i a prg
          -- this HO aspect is problematic (thus the ctx parameter)  
  ApplyW :: (i -> a -> prg) -> Write ctx mem ref i a prg
  VectorW :: i {- really length-} -> (mem a) -> Write ctx mem ref i a prg
  AppendW :: Write ctx mem ref i a prg -> i -> Write ctx mem ref i a prg 
  

---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------

data PushT ctx i b where
  Map      :: (Num i, ctx a) => PushT ctx i a -> (a -> b) -> PushT ctx i b
  Generate :: (Num i, ctx b) => i -> (i -> b) -> PushT ctx i b
  Append   :: Num i => i -> PushT ctx i b -> PushT ctx i b -> PushT ctx i b 


  Return   :: Num i => b -> PushT ctx i b
  Bind     :: PushT ctx i a -> i -> (a -> (PushT ctx i b, i)) -> PushT ctx i b 
---------------------------------------------------------------------------
-- Library functions
---------------------------------------------------------------------------

push :: (Num i, ctx a) => Pull i a -> Push ctx i a
push (Pull ixf n) =
  Push (Generate n ixf) n 


map :: (Num i, ctx a) => (a -> b) -> Push ctx i a -> Push ctx i b
map f (Push p l) = Push (Map p f) l 
  
(++) :: Num i => Push ctx i a -> Push ctx i a -> Push ctx i a
(Push p1 l1) ++ (Push p2 l2) =
  Push (Append l1 p1 p2) (l1 + l2) 


instance Num i => Monad (Push ctx i) where
  return a = Push (Return a) 1
  (Push p l) >>= f = Push p' l'
    where
      -- A trick so that the data types don't depend on the type Push
      g a = let (Push p l) = f a in (p,l)
      h a = let (Push _ l) = f a in l
      p' = Bind p l g
      l' = undefined 
         --unsafeInlinePrim $
         --  do r <- newRef 0
         --     apply p (BindLength h r)
         --     readRef r



---------------------------------------------------------------------------
-- Freeze
---------------------------------------------------------------------------
freeze (Push p l) =
  do
    name <- Allocate l 
    compile p (VectorW l (CMem name)) 
    return $ Pull (\ix -> Index name ix) l 

freeze2 :: (RefMonad m r, PrimMonad m) => Push (Eval m)  Int a -> m (V.Vector a)
freeze2 (Push p l) =
  do
    mem <- M.new l
    eval p (VectorW l mem) 
    V.freeze mem  -- can pull from and maintain same interface! 


---------------------------------------------------------------------------
-- Compile 
---------------------------------------------------------------------------
data CMem a = CMem String
data CRef a = CRef String 
    
class  Compile a  where
  compile :: PushT Compile Index a -> Write Compile CMem CRef Index a (Prg ()) -> Prg ()

  compileW :: Write Compile CMem CRef Index a (Prg ()) -> (Index -> a -> Prg ())
  
  
instance Compile (Exp a) where
  compile (Generate n ixf) = \k -> PFor "v" n $ compileW k (Variable "v") (ixf (Variable "v")) 
  compile (Map p f)   = \k -> compile p (MapW k f)
  compile (Append l p1 p2) = \k -> compile p1 k >> compile p2 (AppendW k l)
  compile (Return a) =  \k -> compileW k 0 a 
  
  compileW (VectorW l (CMem name)) = \i a -> Assign name i a 
  compileW (MapW k f) = \i a -> compileW k i (f a)
  compileW (AppendW k l) = \i a -> compileW k (l+i) a 
  
---------------------------------------------------------------------------
-- Evaluate 
---------------------------------------------------------------------------

class (PrimMonad m)  => Eval m a where
  eval :: (RefMonad m r)
          => PushT (Eval m ) Int a
          -> Write (Eval m ) (M.MVector (PrimState m)) r Int a (m ())
          -> m ()  
  evalW :: (RefMonad m r) => Write (Eval m ) (M.MVector (PrimState m)) r Int a (m ())
           -> (Int -> a -> m ()) 

instance (RefMonad m r, PrimMonad m) => Eval m a where
  eval (Generate n ixf) = \k -> forM_ [0..n-1] $ \i ->  evalW k i (ixf i)
  eval (Map p f)        = \k -> eval p (MapW k f)
  eval (Append l p1 p2) = \k -> eval p1 k >> eval p2 (AppendW k l) 
  eval (Return a)       = \k -> evalW k 0 a 


  evalW (VectorW l mem) = \i a -> M.write mem i a
  evalW (MapW k f)      = \i a -> evalW k i (f a)
  evalW (AppendW k l)   = \i a -> evalW k (l+i) a 



---------------------------------------------------------------------------
--
---------------------------------------------------------------------------



input1 :: Pull Index (Exp Int) 
input1 = Pull (\i -> i) (Literal 128)
input2 :: Pull Int Int 
input2 = Pull (\i -> i) 128

test1 :: (Num i, ctx a) => Pull i a -> Push ctx i a 
test1 =  push  


-- Req NoMonomorphismRestriction 
runTest1 = freeze   (test1 input1 :: Push Compile (Exp Int) (Exp Int)) 
evalTest1 = freeze2 (test1 input2 :: Push (Eval IO) Int Int) 


test2 :: (Num i, ctx a) => Pull i a -> Push ctx i a
test2 p = p1 ++ p1 
  where
    p1 = push p 

runTest2 = freeze   (test2 input1 :: Push Compile (Exp Int) (Exp Int)) 
evalTest2 = freeze2 (test2 input2 :: Push (Eval IO ) Int Int) 
