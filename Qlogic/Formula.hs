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
  , Boolean(..)
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
import Prelude hiding ((&&),(||),not,foldl,foldr)
import qualified Prelude as Prelude
import Data.Typeable
import Data.Foldable
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


comparePropositionalAtom :: PropositionalAtom -> PropositionalAtom -> Ordering
PropositionalAtom (a :: at) `comparePropositionalAtom` PropositionalAtom (b :: bt) 
    | ta == tb = (cast a :: Maybe at) `compare` (cast b :: Maybe at)
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

class Eq a => Boolean a where
  (&&) :: a -> a -> a
  (||) :: a -> a -> a
  not :: a -> a
  true :: a
  false :: a
  bigAnd :: Foldable t => t a -> a
  bigAnd = foldr (&&) true
  bigOr :: Foldable t => t a -> a
  bigOr = foldr (||) false

instance Boolean Bool where
  (&&) = (Prelude.&&)
  (||) = (Prelude.||)
  not = Prelude.not
  true = True
  false = False

instance Eq a => Boolean (Formula a) where
  (&&) = (&&&)
  (||) = (|||)
  not = neg
  true = top
  false = bot

instance PropositionalAtomClass a => PropositionalAtomClass (Formula a)

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

simplify :: Eq a => Formula a -> Formula a
-- ^ performs basic simplification of formulas
simplify (And l)     = bigAnd [simplify e | e <- l]
simplify (Or l)      = bigAnd [simplify e | e <- l]
simplify (a `Iff` b) = simplify a <-> simplify b
simplify (a `Imp` b) = simplify a --> simplify b
simplify (Neg a)     = neg $ simplify a
simplify a           = a

(&&&) :: Eq a => Formula a -> Formula a -> Formula a
-- ^conjunction
Top      &&& b        = b
Bot      &&& _        = Bot
a        &&& Top      = a
_        &&& Bot      = Bot
(And l1) &&& (And l2) = And $ l1 ++ l2
(And l1) &&& b        = And $ l1 ++ [b]
a        &&& (And l2) = And $ a:l2
a        &&& (Neg b)  | a == b    = Bot
a        &&& b        | a == b    = a
a        &&& b        | otherwise = And [a,b]

(|||) :: Eq a => Formula a -> Formula a -> Formula a
-- ^disjunction
Top     ||| _       = Top
Bot     ||| b       = b
_       ||| Top     = Top
a       ||| Bot     = a
(Or l1) ||| (Or l2) = Or $ l1 ++ l2
(Or l1) ||| b       = Or $ l1 ++ [b]
a       ||| (Neg b) | a == b    = Top
a       ||| b       | a == b    = a
a       ||| b       | otherwise = Or [a,b]

(<->) :: Eq a => Formula a -> Formula a -> Formula a
-- ^if and only if
Top <-> b   = b
Bot <-> b   = neg b
a   <-> Top = a
a   <-> Bot = neg a
a   <-> (Neg b)  | a == b    = Bot
a   <-> b        | a == b    = Top
a   <-> b        | otherwise = a `Iff` b

(-->) :: Eq a => Formula a -> Formula a -> Formula a
-- ^implication
Top --> b   = b
Bot --> _   = Top
_   --> Top = Top
a   --> Bot = neg a
a   --> (Neg b) | a == b    = Bot
a   --> b       | a == b    = Top
a   --> b       | otherwise = a `Imp` b

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

atom :: PropositionalAtomClass a => a -> PropositionalFormula
-- ^ lift an atom to a formula
atom = A . PropositionalAtom

oneOrThree :: Eq a => Formula a -> Formula a -> Formula a -> Formula a
-- ^ demands that exacly one or all three formulas hold
oneOrThree p q r = p <-> q <-> r

twoOrThree :: Formula -> Formula -> Formula -> Formula
-- ^ demands that exacly two or all three formulas hold.
twoOrThree p q r = (p ||| q) &&& (p ||| r) &&& (q ||| r)

forall :: (Eq a, Eq b, Foldable t) => t a -> (a -> Formula b) -> Formula b
forall xs f = foldr (\ x fm -> f x &&& fm) top xs 

exist :: (Eq a, Eq b, Foldable t) => t a -> (a -> Formula b) -> Formula b
exist xs f = foldr (\ x fm -> f x ||| fm) bot xs 

ite :: Eq a => Formula a -> Formula a -> Formula a -> Formula a
ite Top t       _ = t
ite Bot _       e = e
ite g   Bot     e = neg g &&& e
ite g   t   Bot   = g &&& t
ite g       t   e = Ite g t e

exactlyOne :: Eq a => [Formula a] -> Formula a
exactlyOne []     = Bot
exactlyOne (x:xs) = ite x (exactlyNone xs) (exactlyOne xs)

exactlyNone  :: Eq a => [Formula a] -> Formula a
exactlyNone xs = forall xs neg

atmostOne :: Eq a => [Formula a] -> Formula a
atmostOne [] = Top
atmostOne [x] = Top
atmostOne fms = bigOr [bigAnd [ neg f2 | f2 <- fms, f1 /= f2] | f1 <- fms]

fm :: Bool -> Formula a
fm True = top
fm False = bot
