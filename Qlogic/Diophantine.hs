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
import qualified Data.Set as Set

data DioVar  = forall a. (DioAtomClass a) => DioVar a
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
                                           where ta    = typeOf a
                                                 tb    = typeOf b
                                                 expeq = ai == bi

instance Eq DioVar where
  DioVar (a :: a) == DioVar (b :: b) =
    typeOf a == typeOf b && ((cast a :: Maybe a) == (cast b :: Maybe a))

instance Ord DioVar where
  DioVar (a :: a) >= DioVar (b :: b) | show ta > show tb  = True
                                     | show ta == show tb = ((cast a :: Maybe a) >= (cast b :: Maybe a))
                                     | otherwise = False
                                     where ta = typeOf a
                                           tb = typeOf b

toFormGen :: (Size -> DioPoly -> (NatFormula, Set.Set DioVar)) -> Size -> DioFormula -> (Formula, Set.Set DioVar)
toFormGen f n (A (Atom a)) = case (cast a :: Maybe DioAtom) of
                               Just (p `Grt` q) -> (truncBots (fst pres) .>. truncBots (fst qres), Set.union (snd pres) (snd qres))
                                                   where pres = f n p
                                                         qres = f n q
                               Just (p `Equ` q) -> (truncBots (fst pres) .=. truncBots (fst qres), Set.union (snd pres) (snd qres))
                                                   where pres = f n p
                                                         qres = f n q
                               Nothing          -> (A (Atom a), Set.empty)
toFormGen f n (p `And` q)  = (fst pres &&& fst qres, Set.union (snd pres) (snd qres))
                                                   where pres = toFormGen f n p
                                                         qres = toFormGen f n q
toFormGen f n (p `Or` q)   = (fst pres ||| fst qres, Set.union (snd pres) (snd qres))
                                                   where pres = toFormGen f n p
                                                         qres = toFormGen f n q
toFormGen f n (p `Imp` q)  = (fst pres --> fst qres, Set.union (snd pres) (snd qres))
                                                   where pres = toFormGen f n p
                                                         qres = toFormGen f n q
toFormGen f n (p `Iff` q)  = (fst pres <-> fst qres, Set.union (snd pres) (snd qres))
                                                   where pres = toFormGen f n p
                                                         qres = toFormGen f n q
toFormGen f n (Neg p)      = (neg (fst pres), snd pres)
                             where pres = toFormGen f n p
toFormGen _ _ Top          = (Top, Set.empty)
toFormGen _ _ Bot          = (Bot, Set.empty)

toFormulaSimp :: Size -> DioFormula -> Formula
-- ^ translates a Diophantine constraint into a propositional formula,
--   where variables are instantiated by values between 0 and n.
toFormulaSimp n = fst . toFormulaSimp' n

toFormulaSimp' :: Size -> DioFormula -> (Formula, Set.Set DioVar)
toFormulaSimp' = toFormGen polyToNatSimp

polyToNatSimp :: Size -> DioPoly -> (NatFormula, Set.Set DioVar)
polyToNatSimp n = pairEmpty . truncBots . bigPlus . map (monoToNatSimp n)
                  where pairEmpty x = (x, Set.empty)

monoToNatSimp :: Size -> DioMono -> NatFormula
monoToNatSimp n (DioMono m vp) = truncBots $ natToFormula m .*. (bigTimes . map (powerToNatSimp n)) vp

powerToNatSimp :: Size -> VPower-> NatFormula
powerToNatSimp n (VPower v m) | m > 0     = natAtom n v .*. powerToNatSimp n (VPower v (m - 1))
                              | otherwise = [Top]

-- Optimisation c of Section 5 in the Fuhs-et-al paper
-- prunes all "numbers" to their maximum length based on
-- the assumption that the value of all variables is at most n
toFormula :: Size -> DioFormula -> Formula
-- ^ translates a Diophantine constraint into a propositional formula,
--   where variables are instantiated by values between 0 and n.
--   this function tracks the maximum value of all subformulas.
--   the length of all vectors is possibly pruned according to these
--   maximum values
toFormula n phi = fst mainResult &&& bigAnd (Set.map (varRestrict n) (snd mainResult))
                  where varRestrict n v = atom $ (natToPoly . (+ 1) . bound) n `Grt` varToPoly v
                        mainResult      = toFormula' n phi

toFormula' :: Size -> DioFormula -> (Formula, Set.Set DioVar)
toFormula' = toFormGen polyToNat

polyToNat :: Size -> DioPoly -> (NatFormula, Set.Set DioVar)
polyToNat n xs = ((truncBots . truncTo (natToBits newmax) . bigPlus . map fst) subresults, Set.unions ((map (snd . snd)) subresults))
  where subresults = map (monoToNat n) xs
        newmax     = (sum . map (fst . snd)) subresults

monoToNat :: Size -> DioMono -> (NatFormula, (Int, Set.Set DioVar))
monoToNat n (DioMono m vp) = (newformula powers, (newmax, Set.unions (map (snd . snd) powers)))
  where newformula = truncBots . truncTo (natToBits newmax) .  ((natToFormula m) .*.) . bigTimes . map fst
        powers     = map (powerToNat n) vp
        newmax     = m * (product . map (fst . snd)) powers

powerToNat :: Size -> VPower -> (NatFormula, (Int, Set.Set DioVar))
powerToNat n (VPower v m) | m > 0     = (natAtom n v .*. powerToNatSimp n (VPower v (m - 1)), ((bound n) ^ m, Set.singleton (DioVar v)))
                          | otherwise = ([Top], (1, Set.empty))

natToPoly :: Int -> DioPoly
natToPoly n = [DioMono n []]

varToPoly :: DioVar -> DioPoly
varToPoly (DioVar v) = [DioMono 1 [VPower v 1]]
