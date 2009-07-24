{-# LANGUAGE DeriveDataTypeable #-}

module Qlogic.ArcSat where

import Prelude hiding ((+), max, not, (&&), (||))
import qualified Prelude as Prelude
import Data.Typeable
import Qlogic.Arctic as Arctic
import Qlogic.Boolean
import Qlogic.Formula
import qualified Qlogic.NatSat as N
import Qlogic.PropositionalFormula
import qualified Qlogic.SatSolver as Sat

type ArcFormula l = (PropFormula l, [PropFormula l])
data ArcBZVec a = InfBit a | BZVec a Int
  deriving (Eq, Ord, Show, Typeable)

instance (Eq a, Ord a, Show a, Typeable a) => PropAtom (ArcBZVec a)

arcToBits :: ArcInt -> Int
arcToBits MinusInf            = 2
arcToBits (Fin n) | n <= 2    = 2
                  | otherwise = succ $ arcToBits $ Fin $ n `div` 2

bitsToArc :: Int -> ArcInt
bitsToArc n = Fin $ 2 ^ (n - 1)

arcToFormula :: Eq l => ArcInt -> ArcFormula l
arcToFormula MinusInf = (Top, [Bot, Bot])
arcToFormula (Fin x)  = (Bot, twoComplement x)

twoComplement :: Eq l => Int -> [PropFormula l]
twoComplement n | n >= 0    = Bot : N.natToFormula n
                | otherwise = Top : if twoPower subresult then map (const Bot) (tail subresult) else subresult
                              where subresult  = map not $ N.natToFormula $ abs n Prelude.+ 1
                                    twoPower x = head x == Top && Prelude.not (null $ tail x) && all (== Bot) (tail x)

padFront :: Int -> ArcFormula l -> ArcFormula l
padFront n (b, xs) = (b, padFront' n xs)

padFront' :: Int -> [PropFormula l] -> [PropFormula l]
padFront' n xs | n == 0    = xs
               | n > 0     = (if null xs then Bot else head xs) : padFront' (n - 1) xs
               | otherwise = error "ArcSat.padFront: Only natural numbers allowed in argument!"

truncFront :: Eq l => ArcFormula l -> ArcFormula l
truncFront (b, xs) = (b, truncFront' xs)

truncFront' :: Eq l => [PropFormula l] -> [PropFormula l]
truncFront' xs | length xs <= 2 = xs
               | otherwise      = if x1 == x2 then truncFront' (x1 : xs') else xs
                                  where x1  = head xs
                                        x2  = head $ tail xs
                                        xs' = tail $ tail xs

truncTo :: Int -> ArcFormula l -> ArcFormula l
truncTo n (b, xs) = (b, truncTo' n xs)

truncTo' :: Int -> [PropFormula l] -> [PropFormula l]
truncTo' n xs | length xs <= Prelude.max 2 n = xs
              | otherwise                    = x1 : truncTo' n xs'
                                               where x1  = head xs
                                                     x2  = head $ tail xs
                                                     xs' = tail $ tail xs

mAdd :: (Eq l, Sat.Solver s l) => ArcFormula l -> ArcFormula l -> N.NatMonad s l (ArcFormula l)
mAdd p@(a, xs) q@(b, ys) | lengthdiff > 0 = mAdd (a, padFront' lengthdiff xs) (b, ys)
                         | lengthdiff < 0 = mAdd (a, xs) (b, padFront' (-1 * lengthdiff) ys)
                         | otherwise      = do c <- N.freshVar
                                               N.enforce [c <-> (p .>=. q)]
                                               let uress = zipWith (ite c) xs ys
                                               vs <- mapM (const $ N.freshVar) [1..length uress]
                                               N.enforce $ zipWith (<->) vs uress
                                               return (a && b, vs)
  where lengthdiff = length ys - length xs

mTimes :: (Ord l, Sat.Solver s l) => ArcFormula l -> ArcFormula l -> N.NatMonad s l (ArcFormula l)
mTimes (a, xs) (b, ys) | lengthdiff > 0 = mTimes (a, padFront' lengthdiff xs) (b, ys)
                       | lengthdiff < 0 = mTimes (a, xs) (b, padFront' (-1 * lengthdiff) ys)
                       | otherwise      = do c <- N.freshVar
                                             N.enforce [c <-> (a || b)]
                                             uress <- N.mAdd xs ys
                                             case uress of
                                               []     -> return (c, [])
                                               u : us -> return (c, map (not c &&) (u' : us))
                                                         where u' = oneOrThree u x y
                                                               x  = if null xs then Bot else head xs
                                                               y  = if null ys then Bot else head xs
  where lengthdiff = length ys - length xs

(.>.) :: Eq l => ArcFormula l -> ArcFormula l -> PropFormula l
(a, xs) .>. (b, ys) | lengthdiff > 0 = (a, padFront' lengthdiff xs) .>. (b, ys)
                    | lengthdiff < 0 = (a, xs) .>. (b, padFront' (-1 * lengthdiff) ys)
                    | otherwise      = b || (not a && ((not x && y) || ((x <-> y) && xs' N..>. ys')))
                                       where x   = if null xs then Bot else head xs
                                             y   = if null ys then Bot else head ys
                                             xs' = if null xs then [] else tail xs
                                             ys' = if null ys then [] else tail ys
                                             lengthdiff = length ys - length xs

(.>=.) :: Eq l => ArcFormula l -> ArcFormula l -> PropFormula l
(a, xs) .>=. (b, ys) | lengthdiff > 0 = (a, padFront' lengthdiff xs) .>=. (b, ys)
                     | lengthdiff < 0 = (a, xs) .>=. (b, padFront' (-1 * lengthdiff) ys)
                     | otherwise      = b || (not a && ((not x && y) || ((x <-> y) && xs' N..>=. ys')))
                                        where x   = if null xs then Bot else head xs
                                              y   = if null ys then Bot else head ys
                                              xs' = if null xs then [] else tail xs
                                              ys' = if null ys then [] else tail ys
                                              lengthdiff = length ys - length xs

(.=.) :: Eq l => ArcFormula l -> ArcFormula l -> PropFormula l
(a, xs) .=. (b, ys) | lengthdiff > 0 = (a, padFront' lengthdiff xs) .=. (b, ys)
                    | lengthdiff < 0 = (a, xs) .=. (b, padFront' (-1 * lengthdiff) ys)
                    | otherwise      = (a <-> b) && bigAnd (zipWith (<->) xs ys)
  where lengthdiff = length ys - length xs

-- arcAtom :: (Eq l, PropAtom a) => N.Size -> a -> ArcFormula l
-- arcAtom size a = nBitVar (N.bits size) a

arcAtom :: (Eq l, PropAtom a) => Int -> a -> ArcFormula l
arcAtom n v = (propAtom $ InfBit v, arcAtom' 1 n v)

arcAtom' :: (Eq l, PropAtom a) => Int -> Int -> a -> [PropFormula l]
arcAtom' i n v | i <= n    = propAtom (BZVec v n) : arcAtom' (i Prelude.+ 1) n v
               | otherwise = []

baseFromVec :: (Ord a, Show a, Typeable a) => ArcBZVec a -> a
baseFromVec (InfBit x)  = x
baseFromVec (BZVec x _) = x
