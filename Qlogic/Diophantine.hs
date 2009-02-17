module Qlogic.Diophantine where

import Qlogic.NatSat
import qualified Qlogic.Formula as F

type DioPoly a = [DioMono a]
data DioMono a = DioMono Int [VPower a]
data VPower a  = VPower a Int
data DioFormula a = Grt (DioPoly a) (DioPoly a)
                  | Equ (DioPoly a) (DioPoly a)
                  | And (DioFormula a) (DioFormula a)
                  | Or (DioFormula a) (DioFormula a)
                  | Imp (DioFormula a) (DioFormula a)
                  | Iff (DioFormula a) (DioFormula a)
                  | Neg (DioFormula a)
                  | Top
                  | Bot

toFormula :: Int -> DioFormula a -> F.Formula (PLVec a)
toFormula n (p `Grt` q) = truncBots (polyToNat n p) .>. truncBots (polyToNat n q)
toFormula n (p `Equ` q) = truncBots (polyToNat n p) .=. truncBots (polyToNat n q)
toFormula n (p `And` q) = toFormula n p F.&&& toFormula n q
toFormula n (p `Or` q)  = toFormula n p F.||| toFormula n q
toFormula n (p `Imp` q) = toFormula n p F.--> toFormula n q
toFormula n (p `Iff` q) = toFormula n p F.<-> toFormula n q
toFormula n (Neg p)     = F.neg $ toFormula n p
toFormula n Top         = F.Top
toFormula n Bot         = F.Bot

polyToNat :: Int -> DioPoly a -> NatFormula (PLVec a)
polyToNat n = truncBots . bigPlus . map (monoToNat n)

monoToNat :: Int -> DioMono a -> NatFormula (PLVec a)
monoToNat n (DioMono m vp) = truncBots $ (natToFormula m) .*. (bigTimes . map (powerToNat n)) vp

powerToNat :: Int -> VPower a -> NatFormula (PLVec a)
powerToNat n (VPower v m) | m > 0     = varToNat n v .*. powerToNat n (VPower v (m - 1))
                          | otherwise = [F.Top]
