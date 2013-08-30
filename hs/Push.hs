
module Push where


import Control.Monad
import Control.Monad.ST
import Control.Monad.Primitive

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M 


---------------------------------------------------------------------------

type Index = Int
type Length = Int 


---------------------------------------------------------------------------
-- Push array
--------------------------------------------------------------------------- 
data Push m a = Push ((Index -> a -> m ()) -> m ()) Length 



---------------------------------------------------------------------------
-- Basic functions on push arrays
---------------------------------------------------------------------------
map :: (a -> b) -> Push m a -> Push m b
map f (Push p l) = Push (\k -> p (\i a -> k i (f a))) l

imap :: (a -> Index -> b) -> Push m a -> Push m b
imap f (Push p l) = Push (\k -> p (\i a -> k i (f a i))) l 

ixmap :: (Index -> Index) -> Push m a -> Push m a
ixmap f (Push p l) = Push (\k -> p (\i a -> k (f i) a)) l 

(++) :: Monad m => Push m a -> Push m a  -> Push m a
(Push f l1) ++ (Push g l2) =
  Push (\k -> f k >> g (\i a -> k (l1 + i) a)) (l1 + l2) 




---------------------------------------------------------------------------
-- write to vector
--------------------------------------------------------------------------- 

freeze :: PrimMonad m => Push m a -> m (V.Vector a)
freeze (Push p l) =
  do
     arr <- M.new l
     p (\i a -> M.write arr i a)
     V.freeze arr 


