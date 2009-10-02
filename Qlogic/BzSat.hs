{-# LANGUAGE DeriveDataTypeable #-}
module Qlogic.BzSat where

import Prelude hiding ((+), max, not, (&&), (||))
import qualified Prelude as Prelude
import qualified Data.List as List
import Data.Typeable
import qualified Qlogic.Assign as A
import Qlogic.Arctic hiding ((<), (<=))
import Qlogic.Boolean
import Qlogic.Formula
import qualified Qlogic.NatSat as N
import qualified Qlogic.IntSat as I
import qualified Qlogic.ArcSat as AS
import Qlogic.PropositionalFormula
import qualified Qlogic.SatSolver as Sat

data Size = Bits Int
          | Bound ArcInt ArcInt
          deriving (Show, Typeable)

instance Eq Size where
  a == b = bound a == bound b

instance Ord Size where
  compare a b = case compare a'' b'' of
                  LT -> LT
                  GT -> GT
                  EQ -> compare a' b'
                where (a', a'') = bound a
                      (b', b'') = bound b

arcToBits :: ArcInt -> Int
arcToBits MinusInf            = 1
arcToBits (Fin n) | n < 0     = arcToBits $ Fin $ abs $ n Prelude.+ 1
                  | n == 0    = 1
                  | n == 1    = 2
                  | otherwise = succ $ arcToBits $ Fin $ n `div` 2

signedBitsToArc :: Int -> ArcInt
signedBitsToArc n = Fin $ (2 ^ (n - 1)) - 1

bits (Bits n)  = n
bits (Bound m n) = Prelude.max (arcToBits m) (arcToBits n)

bound (Bits n) = (Fin (-(k Prelude.+ 1)), Fin k)
  where Fin k = signedBitsToArc n
bound (Bound m n) = (m, n)

lowerbound = fst . bound
upperbound = snd . bound

increment :: Size -> Size
increment (Bits n)    = Bits $ n Prelude.+ 1
increment (Bound m n) = Bound (f m) $ g n
  where f MinusInf = MinusInf
        f (Fin x)  = Fin $ 2 * x
        g MinusInf = Fin 1
        g (Fin x)  = Fin $ (2 * x) Prelude.+ 1

arcToFormula :: Eq l => ArcInt -> AS.ArcFormula l
arcToFormula MinusInf = (Top, [Top])
arcToFormula (Fin x)  = (Bot, I.twoComplement x)

padFrontM :: (Eq l, Sat.Solver s l) => Int -> AS.ArcFormula l -> N.NatMonad s l (AS.ArcFormula l)
padFrontM n (b, xs) = do subresult <- I.padFrontM n xs
                         return (b, subresult)

truncFront :: Eq l => AS.ArcFormula l -> AS.ArcFormula l
truncFront (b, xs) = (b, I.truncFront xs)

truncTo :: Int -> AS.ArcFormula l -> AS.ArcFormula l
truncTo n (b, xs) = (b, I.truncTo n xs)

mAdd :: (Eq l, Sat.Solver s l) => AS.ArcFormula l -> AS.ArcFormula l -> N.NatMonad s l (AS.ArcFormula l)
mAdd p@(a, xs) q@(b, ys) | lengthdiff > 0 = do xs' <- I.padFrontM lengthdiff xs
                                               mAdd (a, xs') (b, ys)
                         | lengthdiff < 0 = mAdd q p
                         | otherwise      = do c1 <- N.maybeFreshVar $ p `mGeq` q
                                               c2 <- N.maybeFreshVar $ return $ a && b
                                               cs <- mapM (N.maybeFreshVar . return) $ zipWith (ite c1) xs ys
                                               return (c2, cs)
  where lengthdiff = length ys - length xs

mTimes :: (Ord l, Sat.Solver s l) => AS.ArcFormula l -> AS.ArcFormula l -> N.NatMonad s l (AS.ArcFormula l)
mTimes p@(a, xs) q@(b, ys) | lengthdiff > 0 = do xs' <- I.padFrontM lengthdiff xs
                                                 mTimes (a, xs') (b, ys)
                           | lengthdiff < 0 = mTimes q p
                           | otherwise      = do c <- N.maybeFreshVar $ return $ (a || b)
                                                 uress' <- I.mAdd xs ys
                                                 uress  <- mapM (N.maybeFreshVar . return . (not c &&)) uress'
                                                 return (c, uress)
  where lengthdiff = length ys - length xs

mGrt :: (Eq l, Sat.Solver s l) => AS.ArcFormula l -> AS.ArcFormula l -> N.NatMonad s l (PropFormula l)
(a, xs) `mGrt` (b, ys) | lengthdiff > 0 = do xs' <- I.padFrontM lengthdiff xs
                                             (a, xs') `mGrt` (b, ys)
                       | lengthdiff < 0 = do ys' <- I.padFrontM (abs lengthdiff) ys
                                             (a, xs) `mGrt` (b, ys')
                       | otherwise      = do subresult <- xs `I.mGrt` ys
                                             return $ b || (not a && subresult)
                                             where lengthdiff = length ys - length xs

mGeq :: (Eq l, Sat.Solver s l) => AS.ArcFormula l -> AS.ArcFormula l -> N.NatMonad s l (PropFormula l)
(a, xs) `mGeq` (b, ys) | lengthdiff > 0 = do xs' <- I.padFrontM lengthdiff xs
                                             (a, xs') `mGeq` (b, ys)
                       | lengthdiff < 0 = do ys' <- I.padFrontM (abs lengthdiff) ys
                                             (a, xs) `mGeq` (b, ys')
                       | otherwise      = do subresult <- xs `I.mGeq` ys
                                             return $ b || (not a && subresult)
                                             where lengthdiff = length ys - length xs

mEqu :: (Eq l, Sat.Solver s l) => AS.ArcFormula l -> AS.ArcFormula l -> N.NatMonad s l (PropFormula l)
p@(a, xs) `mEqu` q@(b, ys) = do subresult <- xs `I.mEqu` ys
                                return $ (a <-> b) && subresult

soundInf :: (Eq l, PropAtom a) => Size -> a -> PropFormula l
soundInf n v = soundInf' (bits n) v

soundInf' :: (Eq l, PropAtom a) => Int -> a -> PropFormula l
soundInf' n v = propAtom (AS.InfBit v) --> bigAnd (map (not . propAtom . AS.BZVec v) [1..n])

-- arcAtom :: (Eq l, PropAtom a) => N.Size -> a -> ArcFormula l
-- arcAtom size a = nBitVar (N.bits size) a

arcAtomM :: (Eq l, Sat.Solver s l, PropAtom a) => Size -> a -> N.NatMonad s l (AS.ArcFormula l)
arcAtomM n v = do N.enforce [soundInf n v]
                  return $ AS.arcAtom (AS.Bits $ bits n) v

eval ::  Ord l => AS.ArcFormula l -> A.Assign l -> ArcInt
eval (f, fs) ass = boolsToInt $ (A.eval f ass, map (flip A.eval ass) fs)

boolsToInt :: (Bool, [Bool]) -> ArcInt
boolsToInt (True, ps)          = if any id ps then error "Qlogic.BzSat.boolsToInt: Incorrect Encoding of MinusInf" else MinusInf
boolsToInt (False, [])         = Fin 0
boolsToInt (False, True : ps)  = Fin $ boolsToInt' ps - (2 ^ length ps)
boolsToInt (False, False : ps) = Fin $ boolsToInt' ps

boolsToInt' :: [Bool] -> Int
boolsToInt' = List.foldl' f 0
              where f n True = 2 * n Prelude.+ 1
                    f n False = 2 * n
