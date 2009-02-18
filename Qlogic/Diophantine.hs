module Qlogic.Diophantine where

import Qlogic.NatSat
import Qlogic.Formula

type DioPoly a = [DioMono a]
data DioMono a = DioMono Int [VPower a]
data VPower a = VPower a Int
data DioAtom a = Grt (DioPoly a) (DioPoly a)
               | Equ (DioPoly a) (DioPoly a)
type DioFormula a = Formula (DioAtom a)

toFormula :: Int -> DioFormula a -> Formula (PLVec a)
toFormula n (Atom (p `Grt` q)) = truncBots (polyToNat n p) .>. truncBots (polyToNat n q)
toFormula n (Atom (p `Equ` q)) = truncBots (polyToNat n p) .=. truncBots (polyToNat n q)
toFormula n (p `And` q)        = toFormula n p &&& toFormula n q
toFormula n (p `Or` q)         = toFormula n p ||| toFormula n q
toFormula n (p `Imp` q)        = toFormula n p --> toFormula n q
toFormula n (p `Iff` q)        = toFormula n p <-> toFormula n q
toFormula n (Neg p)            = neg $ toFormula n p
toFormula n Top                = Top
toFormula n Bot                = Bot

polyToNat :: Int -> DioPoly a -> NatFormula (PLVec a)
polyToNat n = truncBots . bigPlus . map (monoToNat n)

monoToNat :: Int -> DioMono a -> NatFormula (PLVec a)
monoToNat n (DioMono m vp) = truncBots $ natToFormula m .*. (bigTimes . map (powerToNat n)) vp

powerToNat :: Int -> VPower a -> NatFormula (PLVec a)
powerToNat n (VPower v m) | m > 0     = varToNat n v .*. powerToNat n (VPower v (m - 1))
                          | otherwise = [Top]
