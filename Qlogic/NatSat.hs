module Qlogic.NatSat
  (
  -- * Types
  NatFormula
  , PLVec
  , NatAssign
  -- * Operations
  , natToFormula
  , truncBots
  , truncTo
  , natToBits
  , bitsToNat
  , (.+.)
  , bigPlus
  , (.*.)
  , bigTimes
  , (.>.)
  , (.=.)
  , varToNat
  , natAssignment
  ) where

import Qlogic.Formula
import qualified Qlogic.Assign as A
import qualified Qlogic.Tseitin as T
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.List (nub)
import Foreign.Marshal.Utils (fromBool)

type NatFormula a = [Formula a]
data PLVec a = PLVec a Int
  deriving (Eq, Ord, Show)
type NatAssign a = Map.Map a Int

natToFormula :: Int -> NatFormula a
-- ^ transforms a natural number into a list of Top/Bot values
natToFormula n | n == 0    = [Bot]
               | n == 1    = [Top]
               | n < 0     = error "Only natural numbers allowed in argument!"
               | otherwise = natToFormula (n `div` 2) ++ natToFormula (n `mod` 2)

padBots :: Int -> NatFormula a -> NatFormula a
padBots n | n == 0    = id
          | n > 0     = (:) Bot . padBots (n - 1)
          | otherwise = error "Only natural numbers allowed in argument!"

truncBots :: NatFormula a -> NatFormula a
-- ^ removes leading Bottoms from a list of propositional formulas
--   however, the last Bot in a list consisting only of Bots is never removed
truncBots []       = []
truncBots f@[n]    = f
truncBots (Bot:ps) = truncBots ps
truncBots f@(_:_)  = f

truncTo :: Int -> NatFormula a -> NatFormula a
-- ^ If the given list of propositional formulas is longer than n, its length is reduced
--   to n by chopping off the first elements
truncTo _ []                         = []
truncTo n qs@(p:ps) | length qs <= n = qs
                    | otherwise      = truncTo n ps

natToBits :: Int -> Int
-- ^ calculates the necessary length of a list of Top/Bot values for representing
--   the given natural number
natToBits n | n <= 1    = 1
            | otherwise = (succ . natToBits . (`div` 2)) n

bitsToNat :: Int -> Int
bitsToNat n = (2 ^ n) - 1


(.+.) :: NatFormula a -> NatFormula a -> NatFormula a
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

bigPlus :: [NatFormula a] -> NatFormula a
-- ^ calculates the sum of a list of natural numbers in their representation
--   as lists of propositional formulas
bigPlus = foldr (.+.) [Bot]

(.*.) :: NatFormula a -> NatFormula a -> NatFormula a
-- ^ performs multiplication of natural numbers in the representation as a list
--   of propositional formulas
ps .*. []     = []
ps .*. [q]    = map (&&& q) ps
ps .*. (q:qs) = r1 .+. r2
  where r1 = map (&&& q) ps ++ padBots (length qs) []
        r2 = ps .*. qs

bigTimes :: [NatFormula a] -> NatFormula a
-- ^ calculates the product of a list of natural numbers in their representation
--   as lists of propositional formulas
bigTimes = foldr (.*.) [Top]

(.>.) :: NatFormula a -> NatFormula a -> Formula a
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

(.=.) :: NatFormula a -> NatFormula a -> Formula a
-- ^ performs equality comparisons of natural numbers in the representation
--   as a list of propositional formulas
[] .=. []                  = Top
[p] .=. [q]                = p <-> q
ps .=. qs | lengthdiff > 0 = padBots lengthdiff ps .=. qs
          | lengthdiff < 0 = ps .=. padBots (-1 * lengthdiff) qs
          | otherwise      = (head ps <-> head qs) &&& (tail ps .=. tail qs)
   where lengthdiff        = length qs - length ps

-- creates a variable with enough bits to represent n
varToNat :: Int -> a -> NatFormula (PLVec a)
-- ^ creates a "natural number variable" encoded by a list of
--   propositional variables. The length of the list is chosen
--   to be exactly enough in order to represent n
varToNat = nBitVar . natToBits

nBitVar :: Int -> a -> NatFormula (PLVec a)
nBitVar n v | n > 0     = nBitVar (n - 1) v ++ [Atom (PLVec v n)]
            | otherwise = []

baseFromVec :: PLVec a -> a
baseFromVec (PLVec x _) = x

natAssignment :: Ord a => Int -> A.Assign (PLVec a) -> NatAssign a
-- ^ converts a propositional assignment into an assignment for constraints
--   over natural numbers encoded by propositional formulas
natAssignment n = convMap [1..n] . A.toMap
   where convMap ns ass = (Map.fromList . map ((`convKey` ns) . baseFromVec) . Map.keys . firstIndices) ass
                       where firstIndices   = Map.filterWithKey (\(PLVec _ x) _ -> x == 1)
                             convKey k ns = (k, convKey' k ns)
                             convKey' k   = bListToNat . map (fromJust . (`Map.lookup` ass) . PLVec k)
                             bListToNat   = foldl (\x y -> 2 * x + y) 0 . map fromBool
