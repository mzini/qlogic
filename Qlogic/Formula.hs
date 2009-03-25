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
  -- * Operations 
  , simplify
  , atoms
  -- ** Standard Boolean connectives, simplifying
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
--  , isAtom
  ) 
where
import Data.Typeable
import Data.Foldable
import Prelude hiding (foldl, foldr)
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import Data.Set (Set)

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
             | And Formula Formula
             | Or  Formula Formula
             | Iff Formula Formula
             | Ite Formula Formula Formula
             | Imp Formula Formula
             | Neg Formula
             | Top 
             | Bot deriving (Eq, Ord, Typeable, Show)

atoms :: Formula -> Set Atom
atoms (A a) = Set.singleton a
atoms (a `And` b) = atoms a `Set.union` atoms b
atoms (a `Or` b)  = atoms a `Set.union` atoms b
atoms (a `Iff` b) = atoms a `Set.union` atoms b
atoms (Ite a b c) = Set.unions [atoms a, atoms b, atoms c]
atoms (a `Imp` b) = atoms a `Set.union`atoms b
atoms (Neg a)     = atoms a
atoms Top = Set.empty
atoms Bot = Set.empty

simplify :: Formula -> Formula
-- ^ performs basic simplification of formulas
simplify (a `And` b) = simplify a &&& simplify b
simplify (a `Or` b)  = simplify a ||| simplify b
simplify (a `Iff` b) = simplify a <-> simplify b
simplify (a `Imp` b) = simplify a --> simplify b
simplify (Neg a)     = neg $ simplify a
simplify a           = a

(&&&) :: Formula -> Formula -> Formula 
-- ^conjunction
Top &&& b   = b
Bot &&& _   = Bot
a   &&& Top = a
_   &&& Bot = Bot
a   &&& b   = a `And` b

(|||) :: Formula -> Formula -> Formula 
-- ^disjunction
Top ||| _   = Top
Bot ||| b   = b
_   ||| Top = Top
a   ||| Bot = a
a   ||| b   = a `Or` b

(<->) :: Formula -> Formula -> Formula 
-- ^if and only if
Top <-> b   = b
Bot <-> b   = neg b
Top <-> Top = Top
Bot <-> Bot = Bot
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

bigAnd :: Foldable t => t Formula -> Formula
-- ^ conjunction of multiple formulas
bigAnd = foldr (&&&) Top

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
