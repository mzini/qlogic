module Qlogic.NatSat where

import Qlogic.Formula

type NatFormula a = [Formula a]
type PLVec a = (a, Int)

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

plus :: NatFormula a -> NatFormula a -> NatFormula a
plus [] []                  = []
plus [p] [q]                = [p &&& q, neg (p <-> q)]
plus ps qs | lengthdiff > 0 = plus (padBots lengthdiff ps) qs
           | lengthdiff < 0 = plus ps $ padBots (-1 * lengthdiff) qs
           | otherwise      = twoOrThree p q r : oneOrThree p q r : tail rs
  where lengthdiff = length qs - length ps
        rs         = plus (tail ps) (tail qs)
        p          = head ps
        q          = head qs
        r          = head rs

times :: NatFormula a -> NatFormula a -> NatFormula a
times ps []     = []
times ps [q]    = map (&&& q) ps
times ps (q:qs) = plus r1 r2
  where r1 = (map (&&& q) ps) ++ padBots (length qs) []
        r2 = times ps qs

gt :: NatFormula a -> NatFormula a -> Formula a
gt [] []                  = Bot
gt [p] [q]                = p &&& neg q
gt ps qs | lengthdiff > 0 = gt (padBots lengthdiff ps) qs
         | lengthdiff < 0 = gt ps (padBots (-1 * lengthdiff) qs)
         | otherwise      = (p &&& neg q) ||| ((p <-> q) &&& gt (tail ps) (tail qs))
  where lengthdiff        = length qs - length ps
        p                 = head ps
        q                 = head qs

eq :: NatFormula a -> NatFormula a -> Formula a
eq [] []                  = Top
eq [p] [q]                = p <-> q
eq ps qs | lengthdiff > 0 = eq (padBots lengthdiff ps) qs
         | lengthdiff < 0 = eq ps (padBots (-1 * lengthdiff) qs)
         | otherwise      = ((head ps) <-> (head qs)) &&& eq (tail ps) (tail qs)
  where lengthdiff        = length qs - length ps
