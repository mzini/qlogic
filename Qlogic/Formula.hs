{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Qlogic.Formula
  (-- * Types
   Formula(..)
  , PropositionalAtom(..)
  , PropositionalAtomClass(..)
  , PropositionalFormula
  -- * operations
  , simplify
  , atoms
  -- ** standard Boolean connectives, simplifying
  , (|||)
  , (&&&)
  , (-->)
  , (<->)
  , atom
  , neg
  , top
  , bot
  , bigAnd
  , bigOr
  , forall
  , exist
  -- ** non-standard Boolean connectives 
  , oneOrThree
  , twoOrThree
  , exactlyOne
  , atmostOne
  , ite
  , fm
  -- ** utility functions
  , pprintFormula
  , pprintPropositionalAtom
  ) 
where
import Data.Typeable
import Data.Foldable
import Prelude hiding (foldl, foldr)
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import Text.PrettyPrint.HughesPJ

infixr 3 &&&
infixr 2 |||
infixr 1 -->
infixr 1 <->

data PropositionalAtom = forall a. (PropositionalAtomClass a) => PropositionalAtom a deriving Typeable

class (Eq a, Ord a, Show a, Typeable a) => PropositionalAtomClass a  where
            toPropositionalAtom :: a -> PropositionalAtom
            toPropositionalAtom = PropositionalAtom
            fromPropositionalAtom :: PropositionalAtom -> Maybe a
            fromPropositionalAtom (PropositionalAtom a) = cast a


compareAtom :: Atom -> Atom -> Ordering
Atom (a :: at) `compareAtom` Atom (b :: bt) | ta == tb = (cast a :: Maybe at) `compare` (cast b :: Maybe at)
                                            | otherwise = show ta `compare` show tb 
   where ta = typeOf a
         tb = typeOf b

instance Eq PropositionalAtom where
  a == b = a `comparePropositionalAtom` b == EQ

instance Ord PropositionalAtom where
  compare = comparePropositionalAtom

instance Show PropositionalAtom where
  show (PropositionalAtom a) = "PropositionalAtom " ++ show  a

instance PropositionalAtomClass PropositionalAtom

data Formula a = A a
               | And [Formula a]
               | Or  [Formula a]
               | Iff (Formula a) (Formula a)
               | Ite (Formula a) (Formula a) (Formula a)
               | Imp (Formula a) (Formula a)
               | Neg (Formula a)
               | Top
               | Bot deriving (Eq, Ord, Typeable, Show)

type PropositionalFormula = Formula PropositionalAtom

pprintPropositionalAtom :: Show a => a -> Doc
pprintPropositionalAtom = text . show

pprintBinFm :: Show a => String -> Formula a -> Formula a -> Doc
pprintBinFm s a b = parens $ text s <+> (pprintFormula a $$ pprintFormula b)

pprintFormula :: Show a => Formula a -> Doc
pprintFormula (A a)       = pprintPropositionalAtom a
pprintFormula (And l)     = parens $ text "/\\" <+> sep (punctuate (text " ") $ map pprintFormula l)
pprintFormula (Or l)      = parens $ text "\\/" <+> sep (punctuate (text " ") $ map pprintFormula l)
pprintFormula (Iff a b)   = pprintBinFm "<->" a b
pprintFormula (Imp a b)   = pprintBinFm "-->" a b
pprintFormula (Ite a b c) = parens $ text "ite" <+> (pprintFormula a $$ pprintFormula b $$ pprintFormula c)
pprintFormula (Neg a)     = parens $ text "-" <+> (pprintFormula a)
pprintFormula Top         = text "T"
pprintFormula Bot         = text "F"


atoms :: Ord a => Formula a -> Set a
atoms (A a)       = Set.singleton a
atoms (And l)     = Set.unions [atoms e | e <- l]
atoms (Or l)      = Set.unions [atoms e | e <- l]
atoms (a `Iff` b) = atoms a `Set.union` atoms b
atoms (Ite a b c) = Set.unions [atoms a, atoms b, atoms c]
atoms (a `Imp` b) = atoms a `Set.union`atoms b
atoms (Neg a)     = atoms a
atoms Top         = Set.empty
atoms Bot         = Set.empty

simplify :: Formula a -> Formula a
-- ^ performs basic simplification of formulas
simplify (And l)     = bigAnd [simplify e | e <- l]
simplify (Or l)      = bigAnd [simplify e | e <- l]
simplify (a `Iff` b) = simplify a <-> simplify b
simplify (a `Imp` b) = simplify a --> simplify b
simplify (Neg a)     = neg $ simplify a
simplify a           = a

(&&&) :: Formula a -> Formula a -> Formula a
-- ^conjunction
Top      &&& b        = b
Bot      &&& _        = Bot
a        &&& Top      = a
_        &&& Bot      = Bot
(And l1) &&& (And l2) = And $ l1 ++ l2
a        &&& b        = And [a,b]

(|||) :: Formula a -> Formula a -> Formula a
-- ^disjunction
Top     ||| _       = Top
Bot     ||| b       = b
_       ||| Top     = Top
a       ||| Bot     = a
(Or l1) ||| (Or l2) = Or $ l1 ++ l2
a       ||| b       = Or [a,b]

(<->) :: Formula a -> Formula a -> Formula a
-- ^if and only if
Top <-> b   = b
Bot <-> b   = neg b
a   <-> Top = a
a   <-> Bot = neg a
a   <-> b   = a `Iff` b

(-->) :: Formula a -> Formula a -> Formula a
-- ^implication
Top --> b   = b
Bot --> _   = Top
_   --> Top = Top
a   --> Bot = neg a
a   --> b   = a `Imp` b

neg :: Formula a -> Formula a
-- ^negation
neg Bot     = Top
neg Top     = Bot
neg (Neg a) = a
neg a       = Neg a

bot :: Formula a
-- ^ falsity
bot = Bot

top :: Formula a
-- ^ truth
top = Top

bigAnd :: Foldable t => t (Formula a) -> Formula a
-- ^ conjunction of multiple formulas
bigAnd = foldr (&&&) Top

bigOr :: Foldable t => t (Formula a) -> Formula a
-- ^ disjunction of multiple formulas
bigOr = foldr (|||) Bot

atom :: PropositionalAtomClass a => a -> PropositionalFormula
-- ^ lift an atom to a formula
atom = A . PropositionalAtom

oneOrThree :: Formula a -> Formula a -> Formula a -> Formula a
-- ^ demands that exacly one or all three formulas hold
oneOrThree p q r = p <-> q <-> r

twoOrThree :: Formula -> Formula -> Formula -> Formula
-- ^ demands that exacly two or all three formulas hold.
twoOrThree p q r = (p ||| q) &&& (p ||| r) &&& (q ||| r)

forall :: Foldable t => t a -> (a -> Formula b) -> Formula b
forall xs f = foldr (\ x fm -> f x &&& fm) top xs 

exist :: Foldable t => t a -> (a -> Formula b) -> Formula b
exist xs f = foldr (\ x fm -> f x ||| fm) bot xs 

ite :: Formula a -> Formula a -> Formula a -> Formula a
ite Top t       _ = t
ite Bot _       e = e
ite g   Bot     e = neg g &&& e
ite g   t   Bot   = g &&& t
ite g       t   e = Ite g t e

exactlyOne :: [Formula a] -> Formula a
exactlyOne []     = Bot
exactlyOne (x:xs) = ite x (exactlyNone xs) (exactlyOne xs)

exactlyNone  :: [Formula a] -> Formula a
exactlyNone xs = forall xs neg

atmostOne :: Eq a => [Formula a] -> Formula a
atmostOne [] = Top
atmostOne [x] = Top
atmostOne fms = bigOr [bigAnd [ neg f2 | f2 <- fms, f1 /= f2] | f1 <- fms]

fm :: Bool -> Formula a
fm True = top
fm False = bot


-- utility functions

-- isVariable :: Formula -> Bool
-- -- ^ returns 'True' if the given formula is a variable
-- isVariable (PropositionalAtom _) = True
-- isVariable _       = True

-- isPropositionalAtom :: Formula -> Bool
-- -- ^ returns 'True' if the given formula is a variable, 'Top' or 'Bot'
-- isPropositionalAtom (PropositionalAtom _) = True
-- isPropositionalAtom Top     = True
-- isPropositionalAtom Bot     = True
-- isPropositionalAtom _       = False

-- isLiteral :: Formula -> Bool
-- -- ^ returns 'True' if the given formula is a variable or its negation
-- isLiteral (Neg (PropositionalAtom _)) = True
-- isLiteral (PropositionalAtom _)       = True
-- isLiteral _             = False
