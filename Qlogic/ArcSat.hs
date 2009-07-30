{-# LANGUAGE DeriveDataTypeable #-}

module Qlogic.ArcSat where

import Prelude hiding ((+), max, not, (&&), (||))
import qualified Prelude as Prelude
import qualified Data.List as List
import Data.Typeable
import qualified Qlogic.Assign as A
import Qlogic.Arctic hiding ((<), (<=))
import Qlogic.Boolean
import Qlogic.Formula
import qualified Qlogic.NatSat as N
import Qlogic.PropositionalFormula
import qualified Qlogic.SatSolver as Sat

type ArcFormula l = (PropFormula l, [PropFormula l])
data ArcBZVec a = InfBit a | BZVec a Int
  deriving (Eq, Ord, Show, Typeable)

instance (Eq a, Ord a, Show a, Typeable a) => PropAtom (ArcBZVec a)

arcToInt :: ArcInt -> Int
arcToInt MinusInf = 0
arcToInt (Fin n) = n

arcToBits :: ArcInt -> Int
arcToBits MinusInf            = 1
arcToBits (Fin n) | n == 0    = 1
                  | n == 1    = 2
                  | otherwise = succ $ arcToBits $ Fin $ n `div` 2

bitsToArc :: Int -> ArcInt
bitsToArc n = Fin $ (2 ^ (n - 1)) - 1

arcToFormula :: Eq l => ArcInt -> ArcFormula l
arcToFormula MinusInf = (Top, [Bot])
arcToFormula (Fin x)  = (Bot, twoComplement x)

twoComplement :: Eq l => Int -> [PropFormula l]
twoComplement n | n == -1   = [Top]
                | n == 0    = [Bot]
                | n >= 1    = Bot : N.natToFormula n
                | otherwise = Top : (map not $ N.natToFormula $ abs n - 1)

padFront :: Int -> ArcFormula l -> ArcFormula l
padFront n (b, xs) = (b, padFront' n xs)

padFront' :: Int -> [PropFormula l] -> [PropFormula l]
padFront' n xs | n == 0    = xs
               | n > 0     = (if null xs then Bot else head xs) : padFront' (n - 1) xs
               | otherwise = error "ArcSat.padFront: Only natural numbers allowed in argument!"

-- AS: TODO: keine frische Variable für sehr simple (head xs) Fälle
padFrontM' :: (Eq l, Sat.Solver s l) => Int -> [PropFormula l] -> N.NatMonad s l [PropFormula l]
padFrontM' n xs | n == 0    = return xs
                | n > 0     = if null xs then return $ replicate n Bot else
                              do c <- N.maybeFreshVar $ return $ head xs
                                 return $ replicate n c ++ (c : tail xs)
                | otherwise = error "ArcSat.padFrontM: Only natural numbers allowed in argument!"

-- truncFront :: Eq l => ArcFormula l -> ArcFormula l
-- truncFront (b, xs) = (b, truncFront' xs)
-- 
-- truncFront' :: Eq l => [PropFormula l] -> [PropFormula l]
-- truncFront' xs | length xs <= 2 = xs
--                | otherwise      = if x1 == x2 then truncFront' (x1 : xs') else xs
--                                   where x1  = head xs
--                                         x2  = head $ tail xs
--                                         xs' = tail $ tail xs

truncTo :: Int -> ArcFormula l -> ArcFormula l
truncTo n (b, xs) = (b, truncTo' n xs)

truncTo' :: Int -> [PropFormula l] -> [PropFormula l]
truncTo' n xs | length xs <= Prelude.max 1 n = xs
              | otherwise                    = truncTo' n xs'
                                               where x1  = head xs
                                                     xs' = tail xs

mAdd :: (Eq l, Sat.Solver s l) => ArcFormula l -> ArcFormula l -> N.NatMonad s l (ArcFormula l)
mAdd p@(a, xs) q@(b, ys) | lengthdiff > 0 = do xs' <- padFrontM' lengthdiff xs
                                               mAdd (a, xs') (b, ys)
                         | lengthdiff < 0 = mAdd q p
                         | otherwise      = do c1 <- N.maybeFreshVar $ p .>=. q
                                               c2 <- N.maybeFreshVar $ return $ a && b
                                               cs <- mapM (N.maybeFreshVar . return) $ zipWith (ite c1) xs ys
                                               return (c2, cs)
  where lengthdiff = length ys - length xs

mTimes :: (Ord l, Sat.Solver s l) => ArcFormula l -> ArcFormula l -> N.NatMonad s l (ArcFormula l)
mTimes p@(a, xs) q@(b, ys) | lengthdiff > 0 = do xs' <- padFrontM' lengthdiff xs
                                                 mTimes (a, xs') (b, ys)
                           | lengthdiff < 0 = mTimes q p
                           | otherwise      = do c <- N.maybeFreshVar $ return $ (a || b)
                                                 uress' <- N.mAdd xs ys
                                                 let uress = N.padBots (1 Prelude.+ length xs - length uress') uress'
                                                 case uress of
                                                   []     -> return (c, [])
                                                   u : us -> do cu <- N.maybeFreshVar $ return $ oneOrThree u x y
                                                                cs <- mapM (N.maybeFreshVar . return . (not c &&)) (cu : us)
                                                                return (c, cs)
                                                                where x  = if null xs then Bot else head xs
                                                                      y  = if null ys then Bot else head ys
  where lengthdiff = length ys - length xs

(.>.) :: (Eq l, Sat.Solver s l) => ArcFormula l -> ArcFormula l -> N.NatMonad s l (PropFormula l)
(a, xs) .>. (b, ys) | lengthdiff > 0 = do xs' <- padFrontM' lengthdiff xs
                                          (a, xs') .>. (b, ys)
                    | lengthdiff < 0 = do ys' <- padFrontM' (abs lengthdiff) ys
                                          (a, xs) .>. (b, ys')
                    | otherwise      = do subresult <- xss `N.mGrt` yss
                                          return $ b || (not a && ((not x && y) || ((x --> y) && subresult)))
                                          where x   = if null xs then Bot else head xs
                                                y   = if null ys then Bot else head ys
                                                xss = if null xs then [] else tail xs
                                                yss = if null ys then [] else tail ys
                                                lengthdiff = length ys - length xs

(.>=.) :: (Eq l, Sat.Solver s l) => ArcFormula l -> ArcFormula l -> N.NatMonad s l (PropFormula l)
(a, xs) .>=. (b, ys) | lengthdiff > 0 = do xs' <- padFrontM' lengthdiff xs
                                           (a, xs') .>=. (b, ys)
                     | lengthdiff < 0 = do ys' <- padFrontM' (abs lengthdiff) ys
                                           (a, xs) .>=. (b, ys')
                     | otherwise      = do subresult <- xss `N.mGeq` yss
                                           return $ b || (not a && ((not x && y) || ((x --> y) && subresult)))
                                           where x   = if null xs then Bot else head xs
                                                 y   = if null ys then Bot else head ys
                                                 xss = if null xs then [] else tail xs
                                                 yss = if null ys then [] else tail ys
                                                 lengthdiff = length ys - length xs

(.=.) :: (Eq l, Sat.Solver s l) => ArcFormula l -> ArcFormula l -> N.NatMonad s l (PropFormula l)
p@(a, xs) .=. q@(b, ys) | lengthdiff > 0 = do xs' <- padFrontM' lengthdiff xs
                                              (a, xs') .=. (b, ys)
                        | lengthdiff < 0 = q .=. p
                        | otherwise      = return $ (a <-> b) && bigAnd (zipWith (<->) xs ys)
  where lengthdiff = length ys - length xs

soundInf :: (Eq l, PropAtom a) => ArcInt -> a -> PropFormula l
soundInf n v = soundInf' (arcToBits n) v

soundInf' :: (Eq l, PropAtom a) => Int -> a -> PropFormula l
soundInf' n v = propAtom (InfBit v) --> bigAnd (map (not . propAtom . BZVec v) [1..n])

-- arcAtom :: (Eq l, PropAtom a) => N.Size -> a -> ArcFormula l
-- arcAtom size a = nBitVar (N.bits size) a

arcAtom :: (Eq l, PropAtom a) => Int -> a -> ArcFormula l
arcAtom n v = (propAtom $ InfBit v, arcAtom' 1 n v)

arcAtomM :: (Eq l, Sat.Solver s l, PropAtom a) => ArcInt -> a -> N.NatMonad s l (ArcFormula l)
arcAtomM n v = do N.enforce [soundInf n v]
                  return $ arcAtom (arcToBits n) v

arcAtom' :: (Eq l, PropAtom a) => Int -> Int -> a -> [PropFormula l]
arcAtom' i n v | i <= n    = propAtom (BZVec v n) : arcAtom' (i Prelude.+ 1) n v
               | otherwise = []

baseFromVec :: (Ord a, Show a, Typeable a) => ArcBZVec a -> a
baseFromVec (InfBit x)  = x
baseFromVec (BZVec x _) = x

eval ::  Ord l => ArcFormula l -> A.Assign l -> ArcInt
eval (f, fs) ass = boolsToInt $ (A.eval f ass, map (flip A.eval ass) fs)

boolsToInt :: (Bool, [Bool]) -> ArcInt
boolsToInt (True, ps)          = if any id ps then error "Qlogic.ArcSat.boolsToInt: Incorrect Encoding of MinusInf" else MinusInf
boolsToInt (False, [])         = Fin 0
boolsToInt (False, True : ps)  = Fin $ boolsToInt' ps - (2 ^ length ps)
boolsToInt (False, False : ps) = Fin $ boolsToInt' ps

boolsToInt' :: [Bool] -> Int
boolsToInt' = List.foldl' f 0
              where f n True = 2 * n Prelude.+ 1
                    f n False = 2 * n
