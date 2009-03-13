{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Qlogic.Diophantine
  (
  -- * Types
  DioFormula
  , DioAtom(..)
  , DioPoly
  , DioMono(..)
  , VPower(..)
  -- * Operations
  , toFormulaSimp
  , toFormula
  ) where

import Qlogic.NatSat
import Qlogic.Formula
import Data.Typeable


data VPower  = forall a. (DioAtomClass a) => VPower a Int deriving Typeable
data DioMono = DioMono Int [VPower] 
               deriving (Eq, Ord, Show, Typeable)
type DioPoly = [DioMono]                
data DioAtom = Grt DioPoly DioPoly
             | Equ DioPoly DioPoly 
               deriving (Eq, Ord, Show, Typeable)

class AtomClass a => DioAtomClass a
instance AtomClass DioAtom
type DioFormula = Formula 

instance Show VPower where 
  show (VPower a i) = "VPower " ++ show a ++ " " ++ show i

instance Eq VPower where 
  VPower (a :: a) ai == VPower (b :: b) bi = 
    ai == bi && typeOf a == typeOf b && ((cast a :: Maybe a) == (cast b :: Maybe a))

instance Ord VPower where 
  VPower (a :: a) ai >= VPower (b :: b) bi | ai > bi  = True
                                          | expeq && show ta > show tb = True
                                          | expeq && show ta == show tb = ((cast a :: Maybe a) >= (cast b :: Maybe a))
                                          | otherwise = False
                                          where ta = typeOf a
                                                tb = typeOf b
                                                expeq = ai == bi

toFormulaGen :: (Int -> DioPoly -> NatFormula) -> Int -> DioFormula -> Formula
toFormulaGen f n (A (Atom a))    = case (cast a :: Maybe DioAtom) of 
                                     Just (p `Grt` q)  -> truncBots (f n p) .>. truncBots (f n q)
                                     Just (p `Equ` q)  -> truncBots (f n p) .=. truncBots (f n q)
                                     Nothing           -> (A (Atom a))
toFormulaGen f n (p `And` q)        = toFormulaGen f n p &&& toFormulaGen f n q
toFormulaGen f n (p `Or` q)         = toFormulaGen f n p ||| toFormulaGen f n q
toFormulaGen f n (p `Imp` q)        = toFormulaGen f n p --> toFormulaGen f n q
toFormulaGen f n (p `Iff` q)        = toFormulaGen f n p <-> toFormulaGen f n q
toFormulaGen f n (Neg p)            = neg $ toFormulaGen f n p
toFormulaGen _ _ Top                = Top
toFormulaGen _ _ Bot                = Bot

toFormulaSimp :: Int -> DioFormula -> Formula
-- ^ translates a Diophantine constraint into a propositional formula,
--   where variables are instantiated by values between 0 and n.
toFormulaSimp = toFormulaGen polyToNatSimp

polyToNatSimp :: Int -> DioPoly -> NatFormula
polyToNatSimp n = truncBots . bigPlus . map (monoToNatSimp n)

monoToNatSimp :: Int -> DioMono -> NatFormula
monoToNatSimp n (DioMono m vp) = truncBots $ natToFormula m .*. (bigTimes . map (powerToNatSimp n)) vp

powerToNatSimp :: Int -> VPower-> NatFormula
powerToNatSimp n (VPower v m) | m > 0     = varToNat n v .*. powerToNatSimp n (VPower v (m - 1))
                              | otherwise = [Top]

-- Optimisation c of Section 5 in the Fuhs-et-al paper
-- prunes all "numbers" to their maximum length based on
-- the assumption that the value of all variables is at most n
-- FIXME: AS: [v]<=n muss noch erzwungen werden
toFormula :: Int -> DioFormula -> Formula
-- ^ translates a Diophantine constraint into a propositional formula,
--   where variables are instantiated by values between 0 and n.
--   this function tracks the maximum value of all subformulas.
--   the length of all vectors is possibly pruned according to these
--   maximum values
toFormula = toFormulaGen polyToNat

polyToNat :: Int -> DioPoly -> NatFormula
polyToNat n xs = (truncBots . truncTo (natToBits newmax) . bigPlus . map fst) subresults
  where subresults = map (monoToNat n) xs
        newmax     = (sum . map snd) subresults

monoToNat :: Int -> DioMono -> (NatFormula, Int)
monoToNat n (DioMono m vp) = (newformula powers, newmax)
  where newformula = truncBots . truncTo (natToBits newmax) .  ((natToFormula m) .*.) . bigTimes . map fst
        powers     = map (powerToNat n) vp
        newmax     = m * (product . map snd) powers

powerToNat :: Int -> VPower -> (NatFormula, Int)
powerToNat n (VPower v m) | m > 0     = (varToNat n v .*. powerToNatSimp n (VPower v (m - 1)), n ^ m)
                          | otherwise = ([Top], 1)
