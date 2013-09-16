




{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

{-# LANGUAGE ScopedTypeVariables #-} 
{-# LANGUAGE NoMonomorphismRestriction #-} 

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}

module PushAlternative where


import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive
import Data.RefMonad

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M 

import Prelude hiding (reverse,scanl,(++),map )
import qualified Prelude as P 

-- import Pull

data Pull a = Pull (Index -> a) Length


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

data  Push a  = Push (PushT a)  (Prg Length)

---------------------------------------------------------------------------
-- Base language 
---------------------------------------------------------------------------
data Prg a where
  PFor :: String -> Length -> Prg () -> Prg () -- string is loop variable

  Assign :: String -> Index -> Exp a -> Prg ()

  Allocate :: Length -> Prg String
  Seq :: Prg a -> (a -> Prg b) -> Prg b
  Ret :: a -> Prg a


data CMem a = CMem String
data CRef a = CRef String 



instance Monad Prg where
  return = Ret 
  (>>=)  = Seq


nRef a = do str <- Allocate 1 
            Assign str 0 a 
            return (CRef str) 
rRef (CRef str) = return (Index str 0)
wRef (CRef r) a = Assign r 0 a 
  

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
data Write a  where
  MapW :: Compile b => Write b -> (a -> b) -> Write a           

  ApplyW :: (Index -> a -> Prg ()) -> Write a
  
  VectorW :: Length -> CMem a -> Write a
  AppendW :: Write a -> Index -> Write a

  BindLength :: (a -> Prg Length) -> CRef Length -> Write a 

---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------

data PushT b where
  Map      :: Compile a => PushT a -> (a -> b) -> PushT b
  Generate :: Length -> (Index -> b) -> PushT b
  Append   :: Prg Length -> PushT b -> PushT b -> PushT b 


  Return   :: b -> PushT b
  Bind     :: PushT a -> Prg Length -> (a -> (PushT b, Prg Index)) -> PushT  b 
---------------------------------------------------------------------------
-- Library functions
---------------------------------------------------------------------------


push :: Pull a -> Push a
push (Pull ixf n) =
  Push (Generate n ixf) (return n) -- Now we require prg is monad 


map :: Compile a => (a -> b) -> Push a -> Push b
map f (Push p l) = Push (Map p f) l 



(++) :: (Num i) => Push a -> Push a -> Push a
(Push p1 l1) ++ (Push p2 l2) =
  Push (Append l1 p1 p2) (do l1' <- l1
                             l2' <- l2
                             return $ l1' + l2') 


instance  Monad Push where
  return a = Push (Return a) (return 1)
  (Push p l) >>= f = Push p' l'
    where
      -- A trick so that the data types don't depend on the type Push
      g a = let (Push p l) = f a in (p,l)
      h a = let (Push _ l) = f a in l
      p' = Bind p l g
      -- This has to be expressed in prg alone


      l' =  do r <- nRef 0 
               compileLength p (BindLength h r)
               rRef r

--      (Push q _) = map (\_ -> (0 :: Exp Int)) (Push p l) 


---------------------------------------------------------------------------
-- Freeze
---------------------------------------------------------------------------
freeze (Push p l) =
  do
    l' <- l 
    name <- Allocate l'
    compile p (VectorW l' (CMem name)) 
    return $ Pull (\ix -> Index name ix) l' 


 {- 

freeze2 :: (RefMonad m r, PrimMonad m) => Push (Eval m) m  Int a -> m (V.Vector a)
freeze2 (Push p l) =
  do
    mem <- M.new l
    eval p (VectorW l mem) 
    V.freeze mem  -- can pull from and maintain same interface! 

-} 
---------------------------------------------------------------------------
-- Compile 
---------------------------------------------------------------------------


class  Compile a  where
  compile :: PushT a -> Write a -> Prg ()

  compileW :: Write a -> (Index -> a -> Prg ())
  
  
instance Compile (Exp a) where
  compile (Generate n ixf) = \k -> PFor "v" n $ compileW k (Variable "v") (ixf (Variable "v")) 
  compile (Map p f)   = \k -> compile p (MapW k f)
  compile (Append l p1 p2) = \k ->
    do
      compile p1 k
      l' <- l 
      compile p2 (AppendW k l')
  compile (Return a) =  \k -> compileW k 0 a 
  
  compileW (VectorW l (CMem name)) = \i a -> Assign name i a 
  compileW (MapW k f) = \i a -> compileW k i (f a)
  compileW (AppendW k l) = \i a -> compileW k (l+i) a 


compileLength :: PushT a -> Write a -> Prg ()
compileLength p (BindLength f r) = 

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


