
module Pull (Pull(..),zipPull, PullFrom(..)) where

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as M

type Index = Int
type Length = Int 

---------------------------------------------------------------------------
-- Pull array
---------------------------------------------------------------------------

data Pull a = Pull (Index -> a) Length


zipPull :: Pull a -> Pull b -> Pull (a,b)
zipPull (Pull p1 n1) (Pull p2 n2) = Pull (\i -> (p1 i, p2 i)) (min n1 n2) 

---------------------------------------------------------------------------
-- Convert to Pull array
--------------------------------------------------------------------------- 
class PullFrom c where
  pullFrom :: c a -> Pull a

instance PullFrom V.Vector where
  pullFrom v = Pull (\i -> v V.! i ) (V.length v)

instance PullFrom [] where 
  pullFrom as = Pull (\i -> as !! i) (length as) 

instance PullFrom Pull where
  pullFrom = id 
