module Qlogic.Formula 
  (
   -- * Types
   Formula(..)
   -- * Operations 
   -- ** Boolean Connectives and constructors
  , (|||) 
  , (&&&) 
  , (-->) 
  , (<->) 
  , var 
  , neg 
  , top 
  , bot 
  , bigAnd
  , bigOr
  , oneOrThree
  , twoOrThree
   -- ** Predicates
  , isVariable
  , isLiteral
  , isAtom
  ) 
where
data Formula a = Var a 
               | And (Formula a) (Formula a)
               | Or (Formula a) (Formula a)
               | Iff (Formula a) (Formula a)
               | Imp (Formula a) (Formula a)
               | Neg (Formula a)
               | Top 
               | Bot deriving (Eq, Ord, Show)

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

oneOrThree :: Formula a -> Formula a -> Formula a -> Formula a
oneOrThree p q r = p <-> q <-> r

twoOrThree :: Formula a -> Formula a -> Formula a -> Formula a
twoOrThree p q r = (p ||| q) &&& (p ||| r) &&& (q ||| r)

var :: a -> Formula a 
-- ^ lift a variable to a formula
var = Var

-- utility functions

isVariable :: Formula a -> Bool
-- ^ returns 'True' if the given formula is a variable
isVariable (Var _) = True
isVariable _       = True

isAtom :: Formula a -> Bool
-- ^ returns 'True' if the given formula is a variable, 'Top' or 'Bot'
isAtom (Var _) = True
isAtom Top     = True
isAtom Bot     = True
isAtom _       = False

isLiteral :: Formula a -> Bool
-- ^ returns 'True' if the given formula is a variable or its negation
isLiteral (Neg (Var _)) = True
isLiteral (Var _)       = True
isLiteral _             = False

