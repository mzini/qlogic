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
  , prettyPrint
)
where
import qualified Data.Map as Map
import qualified Data.List as List
import Prelude hiding (lookup)
import Qlogic.Formula hiding ((&&),(||),not)
import Data.Maybe (fromMaybe)
import Text.PrettyPrint.HughesPJ hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as PP

type Assign = Map.Map PropositionalAtom Bool

-- | A 'Binding' maps a variable to a Boolean value
type Binding = (PropositionalAtom, Bool)

lookup :: PropositionalAtom -> Assign -> Maybe Bool
-- ^ lookup the truth-value of a variable from the given assignment, 
-- or return 'Nothing' when the given variable is not bound.
lookup = Map.lookup

(|->) :: PropositionalAtom -> Bool -> Binding
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

fromMap :: Map.Map PropositionalAtom Bool -> Assign
fromMap = id

toMap :: Assign -> Map.Map PropositionalAtom Bool
toMap = id


eval :: PropositionalFormula -> Assign -> Bool
-- ^ evaluate a 'Formula' under the given assignment
eval (A a)       ass = fromMaybe False $ lookup a ass
eval (And l)     ass = all (flip eval ass) l
eval (Or l)      ass = not $ all (not . flip eval ass) l
eval (a `Iff` b) ass = eval a ass == eval b ass
eval (a `Imp` b) ass = not (eval a ass) || eval b ass
eval (Neg a)     ass = not (eval a ass)
eval Top _           = True
eval Bot _           = False
eval (Ite a b c) ass = case eval a ass of 
                         True  -> eval b ass
                         False -> eval c ass


prettyPrint :: Assign -> Doc
prettyPrint = Map.foldWithKey pp PP.empty
  where pp a v d = (pprintPropositionalAtom a <+> text "|->"  <+> (text $ show v)) $$ d
