{-# LANGUAGE DeriveDataTypeable #-}

module Qlogic.NatSat
  (
  -- * Types
  NatFormula
  , PLVec(..)
  , NatAssign
  , Size(..)
  -- * Operations
  , emptyAssignment
  , natToFormula
  , truncBots
  , truncTo
  , natToBits
  , bitsToNat
  , bits
  , bound
  , (.+.)
  , bigPlus
  , (.*.)
  , bigTimes
  , (.>.)
  , (.=.)
  , natAtom
  , natAssignment
  , eval
  ) where

import Qlogic.Formula
import qualified Qlogic.Assign as A
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Typeable

data Size = Bits Int
          | Bound Int
          deriving (Show, Typeable)

natToBits :: Int -> Int
-- ^ calculates the necessary length of a list of Top/Bot values for representing
--   the given natural number
natToBits n | n <= 1    = 1
            | otherwise = (succ . natToBits . (`div` 2)) n

bitsToNat :: Int -> Int
bitsToNat n = (2 ^ n) - 1

bits (Bits n)  = n
bits (Bound n) = natToBits n

bound (Bits n) = bitsToNat n
bound (Bound n) = n

type NatFormula = [Formula]
data PLVec a = PLVec a Int
  deriving (Eq, Ord, Show, Typeable)

instance (Eq a, Ord a, Show a, Typeable a) => AtomClass (PLVec a)

type NatAssign a = Map.Map a Int

emptyAssignment :: NatAssign a
emptyAssignment = Map.empty

natToFormula :: Int -> NatFormula
-- ^ transforms a natural number into a list of Top/Bot values
natToFormula n | n == 0    = [Bot]
               | n == 1    = [Top]
               | n < 0     = error "Only natural numbers allowed in argument!"
               | otherwise = natToFormula (n `div` 2) ++ natToFormula (n `mod` 2)

padBots :: Int -> NatFormula -> NatFormula
padBots n | n == 0    = id
          | n > 0     = (Bot :) . padBots (n - 1)
          | otherwise = error "Only natural numbers allowed in argument!"

truncBots :: NatFormula -> NatFormula
-- ^ removes leading Bottoms from a list of propositional formulas
--   however, the last Bot in a list consisting only of Bots is never removed
truncBots []       = []
truncBots f@[_]    = f
truncBots (Bot:ps) = truncBots ps
truncBots f@(_:_)  = f

truncTo :: Int -> NatFormula -> NatFormula
-- ^ If the given list of propositional formulas is longer than n, its length is reduced
--   to n by chopping off the first elements
truncTo _ []                         = []
truncTo n qs@(_:ps) | length qs <= n = qs
                    | otherwise      = truncTo n ps

(.+.) :: NatFormula -> NatFormula -> NatFormula
-- ^ performs addition of natural numbers in the representation as a list
--   of propositional formulas
[] .+. []                  = []
[p] .+. [q]                = [p &&& q, neg (p <-> q)]
ps .+. qs | lengthdiff > 0 = padBots lengthdiff ps .+. qs
          | lengthdiff < 0 = ps .+. padBots (-1 * lengthdiff) qs
          | otherwise      = twoOrThree p q r : oneOrThree p q r : tail rs
  where lengthdiff = length qs - length ps
        rs         = tail ps .+. tail qs
        p          = head ps
        q          = head qs
        r          = head rs

bigPlus :: [NatFormula] -> NatFormula
-- ^ calculates the sum of a list of natural numbers in their representation
--   as lists of propositional formulas
bigPlus = foldr (.+.) [Bot]

(.*.) :: NatFormula -> NatFormula -> NatFormula
-- ^ performs multiplication of natural numbers in the representation as a list
--   of propositional formulas
_  .*. []     = []
ps .*. [q]    = map (&&& q) ps
ps .*. (q:qs) = r1 .+. r2
  where r1 = map (&&& q) ps ++ padBots (length qs) []
        r2 = ps .*. qs

bigTimes :: [NatFormula] -> NatFormula
-- ^ calculates the product of a list of natural numbers in their representation
--   as lists of propositional formulas
bigTimes = foldr (.*.) [Top]

(.>.) :: NatFormula -> NatFormula -> Formula
-- ^ performs "greater than" comparisons of natural numbers in the representation
--   as a list of propositional formulas
[] .>. []                  = Bot
[p] .>. [q]                = p &&& neg q
ps .>. qs | lengthdiff > 0 = padBots lengthdiff ps .>. qs
          | lengthdiff < 0 = ps .>. padBots (-1 * lengthdiff) qs
          | otherwise      = (p &&& neg q) ||| ((p <-> q) &&& (tail ps .>. tail qs))
   where lengthdiff        = length qs - length ps
         p                 = head ps
         q                 = head qs

(.=.) :: NatFormula -> NatFormula -> Formula
-- ^ performs equality comparisons of natural numbers in the representation
--   as a list of propositional formulas
[] .=. []                  = Top
[p] .=. [q]                = p <-> q
ps .=. qs | lengthdiff > 0 = padBots lengthdiff ps .=. qs
          | lengthdiff < 0 = ps .=. padBots (-1 * lengthdiff) qs
          | otherwise      = (head ps <-> head qs) &&& (tail ps .=. tail qs)
   where lengthdiff        = length qs - length ps

-- creates a variable with enough bits to represent n
natAtom :: (Ord a, Show a, Typeable a) => Size -> a -> NatFormula
-- ^ creates a "natural number variable" encoded by a list of
--   propositional variables. The length of the list is chosen
--   to be exactly enough in order to represent n
natAtom size a = nBitVar (bits size) a

nBitVar :: (Ord a, Show a, Typeable a) => Int -> a -> NatFormula
nBitVar n v | n > 0     = nBitVar (n - 1) v ++ [atom (PLVec v n)]
            | otherwise = []

baseFromVec :: (Ord a, Show a, Typeable a) => PLVec a -> a
baseFromVec (PLVec x _) = x

natAssignment :: (Ord a, Typeable a) => Size -> A.Assign -> NatAssign a
natAssignment s = Map.foldWithKey f Map.empty
  where f _        False natAss = natAss
        f (Atom k) True  natAss = case cast k of 
                                    Just (PLVec var i) -> Map.alter (modifyBit i) var natAss
                                    Nothing            -> natAss
        modifyBit i (Just n) = Just $ n + 2^(bts - i)
        modifyBit i Nothing  = Just $ 2^(bts - i)
        bts = bits s

eval :: NatFormula -> A.Assign -> Int
eval f ass = boolsToInt $ map (flip A.eval ass) f

boolsToInt :: [Bool] -> Int
boolsToInt = List.foldl' f 0
             where f n True = 2 * n + 1
                   f n False = 2 * n
