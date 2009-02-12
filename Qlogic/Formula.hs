module Qlogic.Formula where

data Formula a = Var a 
               | And (Formula a) (Formula a)
               | Or (Formula a) (Formula a)
               | Iff (Formula a) (Formula a)
               | Imp (Formula a) (Formula a)
               | Neg (Formula a)
               | Top 
               | Bot deriving Show

-- custruction and intermediate simplification of formulae

(|||),(&&&),(-->),(<->) :: (Formula a) -> (Formula a) -> (Formula a)

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
Bot --> b   = Top
a   --> Top = Top
a   --> Bot = neg a
a   --> b   = a `Imp` b

neg Bot     = Top
neg Top     = Bot
neg (Neg a) = a
neg a       = Neg a


bot = Bot

top = Top

-- utility functions

isVariable (Var x) = True
isVariable _       = True

isAtom (Var x) = True
isAtom Top     = True
isAtom Bot     = True
isAtom _       = False

