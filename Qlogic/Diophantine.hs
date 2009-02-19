module Qlogic.Diophantine where

import Qlogic.NatSat
import Qlogic.Formula

type DioPoly a = [DioMono a]
data DioMono a = DioMono Int [VPower a]
data VPower a = VPower a Int
data DioAtom a = Grt (DioPoly a) (DioPoly a)
               | Equ (DioPoly a) (DioPoly a)
type DioFormula a = Formula (DioAtom a)

toFormulaGen :: (Int -> DioPoly a -> NatFormula (PLVec a)) -> Int -> DioFormula a -> Formula (PLVec a)
toFormulaGen f n (Atom (p `Grt` q)) = truncBots (f n p) .>. truncBots (f n q)
toFormulaGen f n (Atom (p `Equ` q)) = truncBots (f n p) .=. truncBots (f n q)
toFormulaGen f n (p `And` q)        = toFormulaGen f n p &&& toFormulaGen f n q
toFormulaGen f n (p `Or` q)         = toFormulaGen f n p ||| toFormulaGen f n q
toFormulaGen f n (p `Imp` q)        = toFormulaGen f n p --> toFormulaGen f n q
toFormulaGen f n (p `Iff` q)        = toFormulaGen f n p <-> toFormulaGen f n q
toFormulaGen f n (Neg p)            = neg $ toFormulaGen f n p
toFormulaGen f n Top                = Top
toFormulaGen f n Bot                = Bot

toFormulaSimp :: Int -> DioFormula a -> Formula (PLVec a)
toFormulaSimp = toFormulaGen polyToNatSimp

polyToNatSimp :: Int -> DioPoly a -> NatFormula (PLVec a)
polyToNatSimp n = truncBots . bigPlus . map (monoToNatSimp n)

monoToNatSimp :: Int -> DioMono a -> NatFormula (PLVec a)
monoToNatSimp n (DioMono m vp) = truncBots $ natToFormula m .*. (bigTimes . map (powerToNatSimp n)) vp

powerToNatSimp :: Int -> VPower a -> NatFormula (PLVec a)
powerToNatSimp n (VPower v m) | m > 0     = varToNat n v .*. powerToNatSimp n (VPower v (m - 1))
                              | otherwise = [Top]

-- Optimisation c of Section 5 in the Fuhs-et-al paper
-- prunes all "numbers" to their maximum length based on
-- the assumption that the value of all variables is at most n
toFormula :: Int -> DioFormula a -> Formula (PLVec a)
toFormula = toFormulaGen polyToNat

polyToNat :: Int -> DioPoly a -> NatFormula  (PLVec a)
polyToNat n xs = (truncBots . truncTo (natToBits newmax) . bigPlus . map fst) subresults
  where subresults = map (monoToNat n) xs
        newmax     = (sum . map snd) subresults

monoToNat :: Int -> DioMono a -> (NatFormula (PLVec a), Int)
monoToNat n (DioMono m vp) = (newformula powers, newmax)
  where newformula = truncBots . truncTo (natToBits newmax) .  ((natToFormula m) .*.) . bigTimes . map fst
        powers     = map (powerToNat n) vp
        newmax     = m * (product . map snd) powers

powerToNat :: Int -> VPower a -> (NatFormula (PLVec a), Int)
powerToNat n (VPower v m) | m > 0     = (varToNat n v .*. powerToNatSimp n (VPower v (m - 1)), n ^ m)
                          | otherwise = ([Top], 1)
