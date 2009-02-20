module Qlogic.Assign 
  (
  -- * Bindings
  Binding
  , (|->)
  -- * Assignments
  , Assign
  , lookup
  , empty
  , add
  , fromMap
  , toMap
)
where
import qualified Data.Map as Map
import qualified Data.List as List
import Control.Monad (join)
import Prelude hiding (lookup)
type Assign a = Map.Map a Bool

-- | A 'Binding' maps a variable to a Boolean value
type Binding a = (a, Bool)

lookup :: Ord a => a -> Assign a -> Maybe Bool
-- ^ lookup the truth-value of a variable from the given assignment, 
-- or return 'Nothing' when the given variable is not bound.
lookup = Map.lookup

(|->) :: a -> Bool -> Binding a
-- ^ construct a 'Binding'
a |-> b = (a,b)

empty :: Assign a
-- ^ the empty assignment
empty = Map.empty

add :: Ord a => [Binding a] -> Assign a -> Assign a
-- ^ update the given assignment with a list of bindings, 
-- overwriting previous bindings
add bs ass = List.foldl insert ass bs
    where insert ass' (a,b) = Map.insert a b ass'

fromMap :: Map.Map a Bool -> Assign a
fromMap = id

toMap :: Assign a -> Map.Map a Bool
toMap = id
