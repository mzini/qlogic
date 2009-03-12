{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Qlogic.Formula 
  (-- * Types
   Formula(..) 
  , Atom(..)
  , AtomClass
  -- * Operations 
  , simplify
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
  -- ** non-standard Boolean connectives 
  , oneOrThree
  , twoOrThree
--  , isAtom
  ) 
where
import Data.Typeable

import qualified Data.Maybe as Maybe

class (Eq a, Ord a, Show a, Typeable a) => AtomClass a 
data Atom = forall a. (AtomClass a) => Atom a

instance Eq Atom where
  Atom (a :: a) == Atom (b :: b) | typeOf a == typeOf b = (cast a :: Maybe a) == (cast b :: Maybe a)
                                | otherwise = False 

instance Ord Atom where 
 Atom (a :: a) >= Atom (b :: b) = (ta == tb && (cast a :: Maybe a) >= (cast b :: Maybe a)) || show ta >= show tb 
   where ta = typeOf a 
         tb = typeOf b

instance Show Atom where
  show (Atom a) = "Atom " ++ show a

data Formula = A Atom
             | And Formula Formula
             | Or  Formula Formula
             | Iff Formula Formula
             | Imp Formula Formula
             | Neg Formula
             | Top 
             | Bot deriving (Eq, Ord, Typeable, Show)



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

bigAnd :: [Formula] -> Formula
-- ^ conjunction of multiple formulas
bigAnd = foldr (&&&) Top

bigOr :: [Formula] -> Formula
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
