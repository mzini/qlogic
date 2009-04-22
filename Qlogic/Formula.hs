{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Qlogic.Formula 
  (-- * Types
   Formula(..) 
  , Atom(..)
  , AtomClass(..)
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
  , pprintAtom
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

data Atom = forall a. (AtomClass a) => Atom a

class (Eq a, Ord a, Show a, Typeable a) => AtomClass a  where
            toAtom :: a -> Atom 
            toAtom = Atom 
            fromAtom :: Atom -> Maybe a
            fromAtom (Atom a) = cast a


compareAtom :: Atom -> Atom -> Ordering
Atom (a :: at) `compareAtom` Atom (b :: bt) | ta == tb = (cast a :: Maybe at) `compare` (cast b :: Maybe at)
                                            | otherwise = show ta `compare` show tb 
   where ta = typeOf a 
         tb = typeOf b

instance Eq Atom where
  a == b = a `compareAtom` b == EQ

instance Ord Atom where 
  compare = compareAtom

instance Show Atom where
  show (Atom a) = "Atom " ++ show  a

data Formula = A Atom
             | And [Formula]
             | Or  [Formula]
             | Iff Formula Formula
             | Ite Formula Formula Formula
             | Imp Formula Formula
             | Neg Formula
             | Top 
             | Bot deriving (Eq, Ord, Typeable, Show)

pprintAtom :: Atom -> Doc
pprintAtom (Atom a) = text $ show a

pprintBinFm :: String -> Formula -> Formula -> Doc
pprintBinFm s a b = parens $ text s <+> (pprintFormula a $$ pprintFormula b)

pprintFormula :: Formula -> Doc
pprintFormula (A a)       = pprintAtom a
pprintFormula (And l)     = parens $ text "/\\" <+> sep (punctuate (text " ") $ map pprintFormula l)
pprintFormula (Or l)      = parens $ text "\\/" <+> sep (punctuate (text " ") $ map pprintFormula l)
pprintFormula (Iff a b)   = pprintBinFm "<->" a b
pprintFormula (Imp a b)   = pprintBinFm "-->" a b
pprintFormula (Ite a b c) = parens $ text "ite" <+> (pprintFormula a $$ pprintFormula b $$ pprintFormula c)
pprintFormula (Neg a)     = parens $ text "-" <+> (pprintFormula a)
pprintFormula Top         = text "T"
pprintFormula Bot         = text "F"


atoms :: Formula -> Set Atom
atoms (A a)       = Set.singleton a
atoms (And l)     = Set.unions [atoms e | e <- l]
atoms (Or l)      = Set.unions [atoms e | e <- l]
atoms (a `Iff` b) = atoms a `Set.union` atoms b
atoms (Ite a b c) = Set.unions [atoms a, atoms b, atoms c]
atoms (a `Imp` b) = atoms a `Set.union`atoms b
atoms (Neg a)     = atoms a
atoms Top         = Set.empty
atoms Bot         = Set.empty

simplify :: Formula -> Formula
-- ^ performs basic simplification of formulas
simplify (And l)     = bigAnd [simplify e | e <- l]
simplify (Or l)      = bigAnd [simplify e | e <- l]
simplify (a `Iff` b) = simplify a <-> simplify b
simplify (a `Imp` b) = simplify a --> simplify b
simplify (Neg a)     = neg $ simplify a
simplify a           = a

(&&&) :: Formula -> Formula -> Formula 
-- ^conjunction
Top      &&& b        = b
Bot      &&& _        = Bot
a        &&& Top      = a
_        &&& Bot      = Bot
(And l1) &&& (And l2) = And $ l1 ++ l2
a        &&& b        = And [a,b]

(|||) :: Formula -> Formula -> Formula 
-- ^disjunction
Top     ||| _       = Top
Bot     ||| b       = b
_       ||| Top     = Top
a       ||| Bot     = a
(Or l1) ||| (Or l2) = Or $ l1 ++ l2
a       ||| b       = Or [a,b]

(<->) :: Formula -> Formula -> Formula 
-- ^if and only if
Top <-> b   = b
Bot <-> b   = neg b
a   <-> Top = a
a   <-> Bot = neg a
a   <-> b   = a `Iff` b

(-->) :: Formula -> Formula -> Formula 
-- ^implication
Top --> b   = b
Bot --> _   = Top
_   --> Top = Top
a   --> Bot = neg a
a   --> b   = a `Imp` b

neg :: Formula -> Formula
-- ^negation
neg Bot     = Top
neg Top     = Bot
neg (Neg a) = a
neg a       = Neg a

bot :: Formula
-- ^ falsity
bot = Bot

top :: Formula
-- ^ truth
top = Top

-- MA:TODO: gut so?
bigAnd :: Foldable t => t Formula -> Formula
-- ^ conjunction of multiple formulas
bigAnd = foldr (&&&) Top

-- MA:TODO: gut so?
bigOr :: Foldable t => t Formula -> Formula
-- ^ disjunction of multiple formulas
bigOr = foldr (|||) Bot

atom :: AtomClass a => a -> Formula 
-- ^ lift an atom to a formula
atom = A . Atom

oneOrThree :: Formula -> Formula -> Formula -> Formula
-- ^ demands that exacly one or all three formulas hold
oneOrThree p q r = p <-> q <-> r

twoOrThree :: Formula -> Formula -> Formula -> Formula
-- ^ demands that exacly two or all three formulas hold.
twoOrThree p q r = (p ||| q) &&& (p ||| r) &&& (q ||| r)

forall :: Foldable t => t a -> (a -> Formula) -> Formula
forall xs f = foldr (\ x fm -> f x &&& fm) top xs 

exist :: Foldable t => t a -> (a -> Formula) -> Formula
exist xs f = foldr (\ x fm -> f x ||| fm) bot xs 

ite :: Formula -> Formula -> Formula -> Formula
ite Top t       _ = t
ite Bot _       e = e
ite g   Bot     e = neg g &&& e
ite g   t   Bot   = g &&& t
ite g       t   e = Ite g t e

exactlyOne :: [Formula] -> Formula

exactlyOne []     = Bot
exactlyOne (x:xs) = ite x (exactlyNone xs) (exactlyOne xs)

exactlyNone  :: [Formula] -> Formula
exactlyNone xs = forall xs neg

atmostOne :: [Formula] -> Formula
atmostOne [] = Top
atmostOne [x] = Top
atmostOne fms = bigOr [bigAnd [ neg f2 | f2 <- fms, f1 /= f2] | f1 <- fms]

fm :: Bool -> Formula
fm True = top
fm False = bot


-- utility functions

-- isVariable :: Formula -> Bool
-- -- ^ returns 'True' if the given formula is a variable
-- isVariable (Atom _) = True
-- isVariable _       = True

-- isAtom :: Formula -> Bool
-- -- ^ returns 'True' if the given formula is a variable, 'Top' or 'Bot'
-- isAtom (Atom _) = True
-- isAtom Top     = True
-- isAtom Bot     = True
-- isAtom _       = False

-- isLiteral :: Formula -> Bool
-- -- ^ returns 'True' if the given formula is a variable or its negation
-- isLiteral (Neg (Atom _)) = True
-- isLiteral (Atom _)       = True
-- isLiteral _             = False
