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
  , eval 
)
where
import qualified Data.Map as Map
import qualified Data.List as List
import Control.Monad (join)
import Prelude hiding (lookup)
import Qlogic.Formula
import Data.Maybe (fromMaybe)
type Assign = Map.Map Atom Bool

-- | A 'Binding' maps a variable to a Boolean value
type Binding = (Atom, Bool)

lookup :: Atom -> Assign -> Maybe Bool
-- ^ lookup the truth-value of a variable from the given assignment, 
-- or return 'Nothing' when the given variable is not bound.
lookup = Map.lookup

(|->) :: Atom -> Bool -> Binding
-- ^ construct a 'Binding'
a |-> b = (a,b)

empty :: Assign
-- ^ the empty assignment
empty = Map.empty

add :: [Binding] -> Assign -> Assign
-- ^ update the given assignment with a list of bindings, 
-- overwriting previous bindings
add bs ass = List.foldl insert ass bs
    where insert ass' (a,b) = Map.insert a b ass'

fromMap :: Map.Map Atom Bool -> Assign
fromMap = id

toMap :: Assign -> Map.Map Atom Bool
toMap = id


eval :: Formula -> Assign -> Bool
-- ^ evaluate a 'Formula' under the given assignment
eval (A a)    ass = fromMaybe False $ lookup a ass
eval (a `And` b) ass = eval a ass && eval b ass
eval (a `Or` b)  ass = eval a ass || eval b ass
eval (a `Iff` b) ass = eval a ass == eval b ass
eval (a `Imp` b) ass = not (eval a ass) || eval b ass
eval (Neg a)     ass = not (eval a ass)
eval Top _           = True
eval Bot _           = False
