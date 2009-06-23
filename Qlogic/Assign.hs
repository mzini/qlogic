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
import Prelude hiding (lookup)
import Qlogic.Formula
import Qlogic.PropositionalFormula

import Data.Maybe (fromMaybe)
import Text.PrettyPrint.HughesPJ hiding (empty)
import qualified Text.PrettyPrint.HughesPJ as PP

type A l = Either l PA 
type Assign l = Map.Map (A l) Bool

-- | A 'Binding' maps a variable to a Boolean value
type Binding l = (A l, Bool)

lookup :: Ord l => A l -> Assign l -> Maybe Bool
-- ^ lookup the truth-value of a variable from the given assignment, 
-- or return 'Nothing' when the given variable is not bound.
lookup = Map.lookup

(|->) :: A l -> Bool -> Binding l
-- ^ construct a 'Binding'
a |-> b = (a,b)

empty :: Assign l
-- ^ the empty assignment
empty = Map.empty

add :: Ord l => [Binding l] -> Assign l -> Assign l
-- ^ update the given assignment with a list of bindings, 
-- overwriting previous bindings
add bs ass = foldl insert ass bs
    where insert ass' (a,b) = Map.insert a b ass'

fromMap :: Map.Map (A l) Bool -> Assign l
fromMap = id

toMap :: Assign l -> Map.Map (A l) Bool
toMap = id


eval :: Ord l => PropFormula l -> Assign l -> Bool
-- ^ evaluate a 'Formula' under the given assignment
eval (A a)       ass = fromMaybe False $ lookup (Right a) ass
eval (SL a)      ass = fromMaybe False $ lookup (Left a) ass
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

prettyPrint :: Show l => Assign l -> Doc
prettyPrint = Map.foldWithKey pp PP.empty
  where pp a v d = (text (ppa a) <+> text "|->"  <+> (text $ show v)) $$ d
        ppa (Left a) = "L(" ++ show a ++ ")"
        ppa (Right a) = show a
