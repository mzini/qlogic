module Qlogic.NatSat where

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
natToFormula n | n == 0    = [Bot]
               | n == 1    = [Top]
               | n < 0     = error "Only natural numbers allowed in argument!"
               | otherwise = natToFormula (n `div` 2) ++ natToFormula (n `mod` 2)

padBots :: Int -> NatFormula a -> NatFormula a
padBots n | n == 0    = id
          | n > 0     = (:) Bot . padBots (n - 1)
          | otherwise = error "Only natural numbers allowed in argument!"

truncBots :: NatFormula a -> NatFormula a
truncBots []       = []
truncBots f@[n]    = f
truncBots (Bot:ps) = truncBots ps
truncBots f@(_:_)  = f

(.+.) :: NatFormula a -> NatFormula a -> NatFormula a
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
bigPlus = foldr (.+.) [Bot]

(.*.) :: NatFormula a -> NatFormula a -> NatFormula a
ps .*. []     = []
ps .*. [q]    = map (&&& q) ps
ps .*. (q:qs) = r1 .+. r2
  where r1 = map (&&& q) ps ++ padBots (length qs) []
        r2 = ps .*. qs

bigTimes :: [NatFormula a] -> NatFormula a
bigTimes = foldr (.*.) [Top]

(.>.) :: NatFormula a -> NatFormula a -> Formula a
[] .>. []                  = Bot
[p] .>. [q]                = p &&& neg q
ps .>. qs | lengthdiff > 0 = padBots lengthdiff ps .>. qs
          | lengthdiff < 0 = ps .>. padBots (-1 * lengthdiff) qs
          | otherwise      = (p &&& neg q) ||| ((p <-> q) &&& (tail ps .>. tail qs))
   where lengthdiff        = length qs - length ps
         p                 = head ps
         q                 = head qs

(.=.) :: NatFormula a -> NatFormula a -> Formula a
[] .=. []                  = Top
[p] .=. [q]                = p <-> q
ps .=. qs | lengthdiff > 0 = padBots lengthdiff ps .=. qs
          | lengthdiff < 0 = ps .=. padBots (-1 * lengthdiff) qs
          | otherwise      = (head ps <-> head qs) &&& (tail ps .=. tail qs)
   where lengthdiff        = length qs - length ps

varToNat :: Int -> a -> NatFormula (PLVec a)
varToNat n v | n > 0     = varToNat (n - 1) v ++ [Atom (PLVec v n)]
             | otherwise = []

baseFromVec :: PLVec a -> a
baseFromVec (PLVec x _) = x

natAssignment :: Ord a => Int -> A.Assign (PLVec a) -> NatAssign a
natAssignment n = convMap [1..n] . A.toMap
   where convMap ns ass = (Map.fromList . map ((`convKey` ns) . baseFromVec) . Map.keys . firstIndices) ass
                       where firstIndices   = Map.filterWithKey (\(PLVec _ x) _ -> x == 1)
                             convKey k ns = (k, convKey' k ns)
                             convKey' k   = bListToNat . map (fromJust . (`Map.lookup` ass) . PLVec k)
                             bListToNat   = foldl (\x y -> 2 * x + y) 0 . map fromBool
