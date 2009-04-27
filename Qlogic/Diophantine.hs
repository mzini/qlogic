{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Qlogic.Diophantine
  (
  -- * Types
  DioFormula
  , DioAtom(..)
  , DioPoly
  , DioMono(..)
  , VPower(..)
  -- * Operations
  , toFormula
  , natToPoly
  , add
  , bigAdd
  , mult
  , bigMult
  , simplify
  ) where

import Qlogic.NatSat
import Qlogic.Formula hiding (simplify)
import Control.Monad
import qualified Control.Monad.State.Lazy as State
import qualified Data.List as List
import Data.Typeable
import qualified Data.Set as Set

-- data DioVar  = forall a. (DioAtomClass a) => DioVar a
data VPower a  = VPower a Int
               deriving (Eq, Ord, Show, Typeable)
data DioMono a = DioMono Int [VPower a]
               deriving (Eq, Ord, Show, Typeable)
type DioPoly a = [DioMono a]
data DioAtom a = Grt (DioPoly a) (DioPoly a)
               | Equ (DioPoly a) (DioPoly a)
               deriving (Eq, Ord, Show, Typeable)

class PropositionalAtomClass a => DioAtomClass a
instance PropositionalAtomClass a => PropositionalAtomClass (DioAtom a)
instance PropositionalAtomClass a => PropositionalAtomClass (DioPoly a)
instance PropositionalAtomClass a => PropositionalAtomClass (DioMono a)
type DioFormula a = Formula (DioAtom a)

-- instance Show VPower where
--   show (VPower a i) = "VPower " ++ show a ++ " " ++ show i
--
-- instance Eq VPower where
--   VPower (a :: a) ai == VPower (b :: b) bi =
--     ai == bi && typeOf a == typeOf b && ((cast a :: Maybe a) == (cast b :: Maybe a))
--
-- instance Ord VPower where
--   VPower (a :: a) ai >= VPower (b :: b) bi | ai > bi  = True
--                                            | expeq && show ta > show tb = True
--                                            | expeq && show ta == show tb = ((cast a :: Maybe a) >= (cast b :: Maybe a))
--                                            | otherwise = False
--                                            where ta    = typeOf a
--                                                  tb    = typeOf b
--                                                  expeq = ai == bi
--
-- instance Eq DioVar where
--   DioVar (a :: a) == DioVar (b :: b) =
--     typeOf a == typeOf b && ((cast a :: Maybe a) == (cast b :: Maybe a))
--
-- instance Ord DioVar where
--   DioVar (a :: a) >= DioVar (b :: b) | show ta > show tb  = True
--                                      | show ta == show tb = ((cast a :: Maybe a) >= (cast b :: Maybe a))
--                                      | otherwise = False
--                                      where ta = typeOf a
--                                            tb = typeOf b

dioAtom :: PropositionalAtomClass a => DioFormula a -> PropositionalFormula
dioAtom fm = A (PropositionalAtom fm)

polyAtom :: PropositionalAtomClass a => Size -> DioPoly a -> NatFormula
polyAtom n p = natAtom n $ A (PropositionalAtom p)

monoAtom :: PropositionalAtomClass a => Size -> DioMono a -> NatFormula
monoAtom n m = natAtom n $ A (PropositionalAtom m)

data St a = St { vars :: Set.Set a
               , formulas :: Set.Set (DioFormula a)
               , polys :: Set.Set (DioPoly a)
               , monos :: Set.Set (DioMono a)
               }

type DioSetMonad a r = State.State (St a) r

emptySt :: St a
emptySt = St{vars = Set.empty, formulas = Set.empty, polys = Set.empty, monos = Set.empty}

getVars :: DioSetMonad a (Set.Set a)
getForms :: DioSetMonad a (Set.Set (DioFormula a))
getPolys :: DioSetMonad a (Set.Set (DioPoly a))
getMonos :: DioSetMonad a (Set.Set (DioMono a))

getVars = liftM vars State.get
getForms = liftM formulas State.get
getPolys = liftM polys State.get
getMonos = liftM monos State.get

setVars :: Set.Set a -> DioSetMonad a ()
setVars set = State.modify $ \s -> s{vars = set}

setForms :: Set.Set (DioFormula a) -> DioSetMonad a ()
setForms set = State.modify $ \s -> s{formulas = set}

setPolys :: Set.Set (DioPoly a) -> DioSetMonad a ()
setPolys set = State.modify $ \s -> s{polys = set}

setMonos :: Set.Set (DioMono a) -> DioSetMonad a ()
setMonos set = State.modify $ \s -> s{monos = set}

maybeComputeForm :: PropositionalAtomClass a
                 => DioFormula a
                 -> DioSetMonad a PropositionalFormula
                 -> DioSetMonad a PropositionalFormula
maybeComputeForm fm m =
  do s <- getForms
     (if fm `Set.member` s
      then return (dioAtom fm)
      else setForms (Set.insert fm s) >> m)

maybeComputePoly :: PropositionalAtomClass a
                 => Size
                 -> DioPoly a
                 -> DioSetMonad a NatFormula
                 -> DioSetMonad a NatFormula
maybeComputePoly n fm m =
  do s <- getPolys
     (if fm `Set.member` s
      then return (polyAtom n fm)
      else setPolys (Set.insert fm s) >> m)

maybeComputeMono :: PropositionalAtomClass a
                 => Size
                 -> DioMono a
                 -> DioSetMonad a NatFormula
                 -> DioSetMonad a NatFormula
maybeComputeMono n fm m =
  do s <- getMonos
     (if fm `Set.member` s
      then return (monoAtom n fm)
      else setMonos (Set.insert fm s) >> m)

toFormGen :: DioAtomClass a => (Size -> DioPoly a -> DioSetMonad a NatFormula) -> Size -> DioFormula a -> DioSetMonad a PropositionalFormula
toFormGen f n fm@(A (p `Grt` q)) = maybeComputeForm fm $
                                   do pres <- f n p
                                      qres <- f n q
                                      return $ (dioAtom fm) `Iff` (truncBots pres .>. truncBots qres)
toFormGen f n fm@(A (p `Equ` q)) = maybeComputeForm fm $
                                   do pres <- f n p
                                      qres <- f n q
                                      return $ (dioAtom fm) `Iff` (truncBots pres .=. truncBots qres)
toFormGen f n fm@(And ps)        = maybeComputeForm fm $
                                   do press <- mapM (toFormGen f n) ps
                                      return $ (dioAtom fm) `Iff` (bigAnd press)
toFormGen f n fm@(Or ps)         = maybeComputeForm fm $
                                   do press <- mapM (toFormGen f n) ps
                                      return $ (dioAtom fm) `Iff` (bigOr press)
toFormGen f n fm@(p `Imp` q)     = maybeComputeForm fm $
                                   do pres <- toFormGen f n p
                                      qres <- toFormGen f n q
                                      return $ (dioAtom fm) `Iff` (pres `Imp` qres)
toFormGen f n fm@(p `Iff` q)     = maybeComputeForm fm $
                                   do pres <- toFormGen f n p
                                      qres <- toFormGen f n q
                                      return $ (dioAtom fm) `Iff` (pres `Iff` qres)
toFormGen f n fm@(Ite p q r)     = maybeComputeForm fm $
                                   do pres <- toFormGen f n p
                                      qres <- toFormGen f n q
                                      rres <- toFormGen f n r
                                      return $ (dioAtom fm) `Iff` (Ite pres qres rres)
toFormGen f n fm@(Neg p)         = maybeComputeForm fm $
                                   do pres <- toFormGen f n p
                                      return $ (dioAtom fm) `Iff` (Neg pres)
toFormGen _ _ Top                = return Top
toFormGen _ _ Bot                = return Bot

toFormulaGen :: DioAtomClass a => (Size -> DioFormula a -> DioSetMonad a PropositionalFormula) -> Size -> DioFormula a -> PropositionalFormula
toFormulaGen f n phi = fst mainResult &&& bigAnd (Set.map (varRestrict n) (vars (snd mainResult)))
                       where varRestrict n v = atom $ (natToPoly . (+ 1) . bound) n `Grt` varToPoly v
                             mainResult      = State.runState (f n phi) emptySt

-- toFormulaSimp :: DioAtomClass a => Size -> DioFormula a -> PropositionalFormula
-- -- ^ translates a Diophantine constraint into a propositional formula,
-- --   where variables are instantiated by values between 0 and n.
-- toFormulaSimp = toFormulaGen toFormulaSimp'
--
-- toFormulaSimp' :: DioAtomClass a => Size -> DioFormula a -> DioSetMonad a PropositionalFormula
-- toFormulaSimp' = toFormGen polyToNatSimp
--
-- polyToNatSimp :: DioAtomClass a => Size -> DioPoly a -> DioSetMonad a NatFormula
-- polyToNatSimp n = pairEmpty . truncBots . bigPlus . map (monoToNatSimp n)
--                   where pairEmpty x = (x, Set.empty)
--
-- monoToNatSimp :: DioAtomClass a => Size -> DioMono a -> NatFormula
-- monoToNatSimp n (DioMono m vp) = truncBots $ natToFormula m .*. (bigTimes . map (powerToNatSimp n)) vp
--
-- powerToNatSimp :: DioAtomClass a => Size -> VPower a -> NatFormula
-- powerToNatSimp n (VPower v m) | m > 0     = natAtom n v .*. powerToNatSimp n (VPower v (m - 1))
--                               | otherwise = [Top]

-- Optimisation c of Section 5 in the Fuhs-et-al paper
-- prunes all "numbers" to their maximum length based on
-- the assumption that the value of all variables is at most n
toFormula :: DioAtomClass a => Size -> DioFormula a -> PropositionalFormula
-- ^ translates a Diophantine constraint into a propositional formula,
--   where variables are instantiated by values between 0 and n.
--   this function tracks the maximum value of all subformulas.
--   the length of all vectors is possibly pruned according to these
--   maximum values
toFormula = toFormulaGen toFormula'

toFormula' :: DioAtomClass a => Size -> DioFormula a -> DioSetMonad a PropositionalFormula
toFormula' = toFormGen polyToNat

polyToNat :: DioAtomClass a => Size -> DioPoly a -> DioSetMonad a NatFormula
polyToNat n xs = maybeComputePoly newmax xs $
                 do press <- mapM (monoToNat n) xs
                    return $ zipWith Iff (polyAtom newmax xs) ((truncTo (bits newmax) . bigPlus) press)
                      where newmax = polyBound n xs

monoToNat :: DioAtomClass a => Size -> DioMono a -> DioSetMonad a NatFormula
monoToNat n fm@(DioMono m vp) = maybeComputeMono newmax fm $
                                do press <- mapM (powerToNat n) vp
                                   return $ zipWith Iff (monoAtom newmax fm) (multres press)
                                where multres ps = (truncTo (bits newmax) . bigTimes) (natToFormula m : ps)
                                      newmax     = monoBound n fm

powerToNat :: DioAtomClass a => Size -> VPower a -> DioSetMonad a NatFormula
powerToNat n (VPower v m) | m > 0     = do s <- getVars
                                           setVars (Set.insert v s)
                                           return $ bigTimes (replicate m (natAtom n v))
                          | otherwise = return [Top]

polyBound :: Size -> DioPoly a -> Size
polyBound n = Bound . sum . map (bound . (monoBound n))

monoBound :: Size -> DioMono a -> Size
monoBound n (DioMono m xs) = Bound $ foldr ((*) . bound . powerBound n) m xs

powerBound :: Size -> VPower a -> Size
powerBound n (VPower _ m) = Bound $ (bound n) ^ m

natToPoly :: Int -> DioPoly a
natToPoly n = [DioMono n []]

varToPoly :: a -> DioPoly a
varToPoly v = [DioMono 1 [VPower v 1]]

add :: Eq a => DioPoly a -> DioPoly a -> DioPoly a
add p = shallowSimp . (++) p

bigAdd :: Eq a => [DioPoly a] -> DioPoly a
bigAdd = shallowSimp . concat

mult :: Eq a => DioPoly a -> DioPoly a -> DioPoly a
mult p = bigAdd . map (pmmult p)

pmmult :: Eq a => DioPoly a -> DioMono a -> DioPoly a
pmmult p m = map (mmult m) p

mmult :: Eq a => DioMono a -> DioMono a -> DioMono a
mmult (DioMono m xs) (DioMono n ys) = simpMono $ DioMono (m * n) (xs ++ ys)

bigMult :: Eq a => [DioPoly a] -> DioPoly a
bigMult = foldr mult (natToPoly 1)

simplify :: Eq a => DioPoly a -> DioPoly a
simplify = shallowSimp . map simpMono

shallowSimp :: Eq a => DioPoly a -> DioPoly a
shallowSimp [] = []
shallowSimp ((DioMono n xs):ms) | n == 0    = shallowSimp ms
shallowSimp ((DioMono n xs):ms) | otherwise = (DioMono (foldr addcoeff n (fst ys)) xs):(shallowSimp (snd ys))
                                  where ys                      = List.partition (\(DioMono _ xs') -> xs == xs') ms
                                        addcoeff (DioMono x _) y = x + y

simpMono :: Eq a => DioMono a -> DioMono a
simpMono (DioMono n xs) = DioMono n (simpPower xs)

simpPower :: Eq a => [VPower a] -> [VPower a]
simpPower [] = []
simpPower ((VPower v n):xs) | n == 0    = simpPower xs
simpPower ((VPower v n):xs) | otherwise = (VPower v (foldr addpow n (fst ys))):(simpPower (snd ys))
                                          where ys                    = List.partition (\(VPower w _) -> v == w) xs
                                                addpow (VPower _ y) x = y + x
