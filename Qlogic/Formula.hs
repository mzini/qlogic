module Qlogic.Formula 
  (-- * Types
   Formula(..) 
  -- * Operations 
  , eval 
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
import qualified Qlogic.Assign as Assign
import Qlogic.Assign (Assign)
import Test.QuickCheck 
import qualified Data.Maybe as Maybe
data Formula a = Atom a
               | And (Formula a) (Formula a)
               | Or (Formula a) (Formula a)
               | Iff (Formula a) (Formula a)
               | Imp (Formula a) (Formula a)
               | Neg (Formula a)
               | Top 
               | Bot deriving (Eq, Ord, Show)

simplify :: Formula a -> Formula a
-- ^ performs basic simplification of formulas
simplify (a `And` b) = simplify a &&& simplify b
simplify (a `Or` b)  = simplify a ||| simplify b
simplify (a `Iff` b) = simplify a <-> simplify b
simplify (a `Imp` b) = simplify a --> simplify b
simplify (Neg a)     = neg $ simplify a
simplify a           = a

(&&&) :: Formula a -> Formula a -> Formula a 
-- ^conjunction
Top &&& b   = b
Bot &&& _   = Bot
a   &&& Top = a
_   &&& Bot = Bot
a   &&& b   = a `And` b

(|||) :: Formula a -> Formula a -> Formula a 
-- ^disjunction
Top ||| _   = Top
Bot ||| b   = b
_   ||| Top = Top
a   ||| Bot = a
a   ||| b   = a `Or` b

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

bigAnd :: [Formula a] -> Formula a
-- ^ conjunction of multiple formulas
bigAnd = foldr (&&&) Top

bigOr :: [Formula a] -> Formula a
-- ^ disjunction of multiple formulas
bigOr = foldr (|||) Bot

atom :: a -> Formula a 
-- ^ lift an atom to a formula
atom = Atom

oneOrThree :: Formula a -> Formula a -> Formula a -> Formula a
-- ^ demands that exacly one or all three formulas hold
oneOrThree p q r = p <-> q <-> r

twoOrThree :: Formula a -> Formula a -> Formula a -> Formula a
-- ^ demands that exacly two or all three formulas hold.
twoOrThree p q r = (p ||| q) &&& (p ||| r) &&& (q ||| r)


eval :: Ord a => Formula a -> Assign a -> Bool
-- ^ evaluate a 'Formula' under the given assignment
eval (Atom a)    ass = Maybe.fromMaybe False $ Assign.lookup a ass
eval (a `And` b) ass = eval a ass && eval b ass
eval (a `Or` b)  ass = eval a ass || eval b ass
eval (a `Iff` b) ass = eval a ass == eval b ass
eval (a `Imp` b) ass = not (eval a ass) || eval b ass
eval (Neg a)     ass = not (eval a ass)
eval Top _           = True
eval Bot _           = False

-- utility functions

-- isVariable :: Formula a -> Bool
-- -- ^ returns 'True' if the given formula is a variable
-- isVariable (Atom _) = True
-- isVariable _       = True

-- isAtom :: Formula a -> Bool
-- -- ^ returns 'True' if the given formula is a variable, 'Top' or 'Bot'
-- isAtom (Atom _) = True
-- isAtom Top     = True
-- isAtom Bot     = True
-- isAtom _       = False

-- isLiteral :: Formula a -> Bool
-- -- ^ returns 'True' if the given formula is a variable or its negation
-- isLiteral (Neg (Atom _)) = True
-- isLiteral (Atom _)       = True
-- isLiteral _             = False
