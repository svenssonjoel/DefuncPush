{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}



-- This is the approach described in the paper "Defunctionalizing Push Arrays" 
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
-- Push Language
---------------------------------------------------------------------------
data PushT b where
  Map  :: Expable a => (a -> b) -> PushT a -> PushT b

  -- array creation 
  Generate :: Length -> (Ix -> b) -> PushT b
  Use :: Expable b => CMMem b -> PushT b 

  Force :: Length -> PushT b -> PushT b 

  IMap :: Expable a => (Ix -> a -> b) -> PushT a -> PushT b

  Append :: Length -> PushT b -> PushT b -> PushT b

  Interleave :: PushT b -> PushT b -> PushT b  

  -- Permutations
  Reverse :: PushT b -> PushT b
  Rotate  :: Length -> PushT b -> PushT b 


-- now PushT can be used as the array type (without any Push Wrapper) 
pushLength :: PushT b -> Length
pushLength (Generate l _) = l
pushLength (Use (CMMem _ l)) = l
pushLength (Force l _) = l
pushLength (Map _ p)  = pushLength p
pushLength (IMap _ p)  = pushLength p
pushLength (Append _ p1 p2) = pushLength p1 + pushLength p2
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

apply (Use mem@(CMMem _ n)) =
  \k -> do for_ n $ \i ->
                k i (cmIndex mem i) -- a 

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
             --do a <- read arr ix
                k ix (cmIndex arr ix) -- a 



---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------

generate :: Length -> (Ix -> a) -> PushT a
generate = Generate 

use :: Expable a => CMMem a -> PushT a
use mem = Use mem

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


(++) :: PushT a -> PushT a -> PushT a
p1 ++ p2 = Append l1 p1 p2
  where
    l1 = len p1

interleave :: PushT a -> PushT a -> PushT a
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

freeze :: Expable a =>  PushT a -> CompileMonad (CMMem a)
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
     
force :: PushT a -> PushT a
force p = Force (len p) p 
  
---------------------------------------------------------------------------
-- Things that are hard to do with Push or Pull Arrays, but now "simple"
---------------------------------------------------------------------------

index :: Expable a => PushT a -> Ix -> a
index (Map f p) ix        = f (index p ix)
index (Generate n ixf) ix = ixf ix

index (Use mem) ix        = cmIndex mem ix -- read mem ix

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

takeP n vec = push $ takePull n (convert vec)

dropP n vec = push $ dropPull n (convert vec)

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

instance  Num (Expr Float)  where
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

cond :: Expr Bool -> CM () -> CM () -> CM ()
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

input = Pull id 16

simple1 :: (Expable a, Num a) => Pull a -> PushT a
simple1 = map (+1) . force . push 

compileSimple1 = runCM 0 $ toVector ( simple1 input :: PushT (Expr Int))



-- Example without pull arrays entirely
myVec = CMMem "input"  10 

usePrg :: (Expable b,  Num b) => PushT b
usePrg = rotate 3 $ reverse $ map (+1) (use myVec)

compileUse = runCM 0 $ toVector (usePrg :: PushT (Expr Int))

ex1 :: (Expable b,  Num b) => PushT b -> PushT b
ex1 = rotate 3 . reverse . map (+1) 
      
compileEx1 = runCM 0 $ toVector ((ex1 arr) :: PushT (Expr Int))
  where arr = use myVec

saxpy :: Expr Float
       -> PushT (Expr Float)
       -> PushT (Expr Float)
       -> PushT (Expr Float)
saxpy a xs ys = zipWith f xs ys
  where
    f x y = a * x + y


i1, i2 :: CMMem (Expr Float)
i1 = CMMem "input1" 10 
i2 = CMMem "input2" 10

compileSaxpy = runCM 0 $
               toVector (let as = use i1
                             bs = ex1 $ use i2 
                         in saxpy 2 as bs)
  
compileSaxpy' = runCM 0 $
                toVector (let as = use i1
                              bs = use i2
                          in saxpy 1 as bs)



zipWith :: (Expable a, Expable b) => (a -> b -> c)
         -> PushT a
         -> PushT b
         -> PushT c
zipWith f a1 a2 =
  imap (\i a -> f a (index a2 i)) a1




{-
Allocate "v0" 10 :>>:
For "v1" 10 (
  Read "input1" v1 "v2" :>>:
  Write "v0" v1 ((1.0 * v2) + input2[v1])
  )

-}

avg a b = (a + b) `div_` 2

stencil vec = Generate 1 (\_ -> index vec 0 `div_` 2) ++
               zipWith avg c1 c2 ++
               Generate 1 (\_ -> index vec (l - 1) `div_` 2)
  where c1 = dropP 1 vec
        c2 = takeP (l - 1) vec
        l  = len vec

compileStencil = runCM 0 $
                 toVector (stencil (stencil (use i1)))
  where i1 = CMMem "input1" 10 

---------------------------------------------------------------------------
-- Touch entire PushT data type

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
                        
