module Qlogic.Formula where

data Formula a = Var a 
               | And (Formula a) (Formula a)
               | Or (Formula a) (Formula a)
               | Iff (Formula a) (Formula a)
               | Imp (Formula a) (Formula a)
               | Neg (Formula a)
               | Top 
               | Bot deriving (Eq, Ord, Show)

-- custruction and intermediate simplification of formulae

(|||),(&&&),(-->),(<->) :: Formula a -> Formula a -> Formula a

Top &&& b   = b
Bot &&& _   = Bot
a   &&& Top = a
_   &&& Bot = Bot
a   &&& b   = a `And` b

Top ||| _   = Top
Bot ||| b   = b
_   ||| Top = Top
a   ||| Bot = a
a   ||| b   = a `Or` b


Top <-> b   = b
Bot <-> b   = neg b
a   <-> Top = a
a   <-> Bot = neg a
a   <-> b   = a `Iff` b


Top --> b   = b
Bot --> _   = Top
_   --> Top = Top
a   --> Bot = neg a
a   --> b   = a `Imp` b

neg :: Formula a -> Formula a
neg Bot     = Top
neg Top     = Bot
neg (Neg a) = a
neg a       = Neg a

top,bot :: Formula a
bot = Bot

top = Top


bigAnd :: [Formula a] -> Formula a
bigAnd = foldr (&&&) Top

var :: a -> Formula a 
var = Var

-- utility functions

isAtom, isVariable :: Formula a -> Bool

isVariable (Var _) = True
isVariable _       = True

isAtom (Var _) = True
isAtom Top     = True
isAtom Bot     = True
isAtom _       = False

isLiteral (Neg (Var _)) = True
isLiteral (Var _)       = True
isLiteral _             = False

