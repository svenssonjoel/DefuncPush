




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


  --BindW :: (a -> (PushTM b,Prg Length)) -> Prg Length -> Write b -> CRef Length -> Write a
  --BindLength :: (a -> Prg Length) -> CRef Length -> Write a 

---------------------------------------------------------------------------
-- Push Language
---------------------------------------------------------------------------

data PushT b where
  Map      :: Compile a => PushT a -> (a -> b) -> PushT b
  Generate :: Length -> (Index -> b) -> PushT b
  Append   :: Prg Length -> PushT b -> PushT b -> PushT b 
  Concat   :: PushT (PushT a) -> PushT a 

--data PushTM b where 
--  Return   :: b -> PushTM b
--  Bind     :: (Compile a) => (PushT a, Prg Length)  -> (a -> (PushTM b, Prg Index)) -> PushTM  b 

--instance Monad PushTM  where
--  return = Return
--  (Return a) >>= k = k a
   -- k :: b -> PushTM c
   -- h :: a -> (PushTM b, Prg Length)
   -- l :: Prg Length
   -- pta :: PushT a 
--  (Bind (pta,m)  h) >>= k = Bind (pta,m)  (\x ->  let (ptb,l) = h x
--                                                  in (do b <- ptb 
--                                                         k b,l ))

--instance Monad Push where
--  return a = Push (return a) (return 1)
--  pa >>= k = Push ((pushF pa) >>= (\x -> pushF (k x)))

--             (return 10)
             -- 'return 10' is a cheat!
             -- Want it to be (compile pa (BindLength k something))
             -- Big quesion is, can I run compile in this monad instance?  

--pushF :: Push a -> PushTM a
--pushF (Push p _) = p
--pushL :: Push a -> Prg Length
--pushL (Push _ l) = l 


-- Odd type
--liftPTM :: Compile a => PushT a -> Prg Length -> PushTM a
--liftPTM  p l = Bind (p,l) (\a -> (Return a,l))

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

-- instance Monad Push where
--   return a = Push (Return a) (return 1)
--   (Push (Return a) l)  >>= k = k a
--   (Push (Bind pt l h) m) >>= k =
--     Push (Bind pt m (\x -> (let (y,z) = h x
--                             in Bind (Return y) z y' <- y 
--                               let (Push p' l') = k y'
--                               p', l)))
--          (return 10) -- Cheat!
  
-- instance  Monad Push where
--   return a = Push (Return a) (return 1)
--   (Push p l) >>= f = Push p' l'
--     where
--       -- A trick so that the data types don't depend on the type Push
--       g a = let (Push p l) = f a in (p,l)
--       h a = let (Push _ l) = f a in l
--       p' = Bind p l g
--       -- This has to be expressed in prg alone


--       l' =  do r <- nRef 0 
--                compile p (BindLength h r)
--                rRef r

concat :: Push (Push a) -> Push a
concat (Push p l) =
  Push (Concat (pushP p)) (l {- cheat -} )
    where
      pushP :: PushT (Push a) -> PushT (PushT a)
      pushP p =  
    
  
-- where
--     q k = do r <- newRef 0
--              p $ \i a ->
--                do s <- readRef r
--                   let (Push q' m) = a
--                   q' (\j b -> k (s+j) b)
--                   writeRef r (s + m)
--     l' = unsafeInlinePrim $
--          do r <- newRef 0
--             p $ \_ a -> 
--               do let (Push _ l'') = a
--                  modifyRef r (+l'')
--             readRef r


---------------------------------------------------------------------------
-- Freeze
---------------------------------------------------------------------------
--freeze (Push p l) =
--  do
--    l' <- l 
--    name <- Allocate l'
--    let (a,prg) = compileM p (VectorW l' (CMem name))
--    prg
--    return $ Pull (\ix -> Index name ix) l' 


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


--compileM :: Compile a => Supply Int -> PushTM a -> Write a -> (CArray a, Prg ())
--compileM s (Return a) k = (arr, do allocate arr  
--                                   assign arr (injectE (0 :: Exp Int)) a )
--    where
--      i = supplyValue s
--      arr  = mkArray i (injectE (1 :: Exp Int)) -- CArray $ "arr" P.++ show i


--compileM s (Bind (ma,l) h) k = compileW s1 ma (BindW h l k cref) --  undefined 
--    where
      --(arr,prg1) = compile s ma wf

      -- need to compile a "length program" and a "compute program"
      -- 

      -- 
        

--      v2 = supplyValue s2
--      cref = mkRef v2 (injectE 0) 
        
--      (s1,s2) = split2 s 
      --v1 = supplyValue s1
      --carr@(CArray nom) = CArray $ "arr" P.++ show v1
      --wf = VectorW l (CMem nom) 


compileW :: Compile a => Supply Int -> PushT a -> Write a -> (CArray a,Prg ())
compileW s p k = undefined 

compile :: Compile a => Supply Int -> PushT a -> Write a -> (CArray a, Prg ())
compile s p k = undefined 
      
  

      
                          
  --compileM s (Bind ma h) k = 
  --  (b,prg1 `Seq_` prg2)  
  --  where 
  --   (a,prg1) = compile ma k
  --   (b,prg2) = compileM (h a) k 

{-
class  Compile a  where
  
  compile :: PushT a -> Write a -> (a,Prg ())

  compileM :: PushTM a -> Write a -> (a,Prg ())
  
  compileW :: Write a -> Index -> a -> Prg ()
  

instance Compile (Exp a) where
  compile (Generate n ixf) k =  (Variable "dummy", PFor "v" n $ compileW k (Variable "v") (ixf (Variable "v")))
  compile (Map p f)  k  =  compileM p (MapW k f)
  compile (Append l p1 p2) k = (a,prg) 
    where
      (a,prg1) = compileM p1 k
      --l' <- l  
      -- (b,prg2) 

      prg = do
        prg1 
        l' <- l
        let (b,prg2) = compileM p2 (AppendW k l')
        prg2     
  

  
  compileW (VectorW l (CMem name)) = \i a -> Assign name i a 
  compileW (MapW k f) = \i a -> compileW k i (f a)
  compileW (AppendW k l) = \i a -> compileW k (l+i) a 
-} 
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
