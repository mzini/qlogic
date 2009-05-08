{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Qlogic.Diophantine
  (
  -- * Types
  DioFormula
  , DioAtom(..)
  , DioPoly
  , DioMono(..)
  , VPower(..)
  , DioVar(..)
  , DioVarClass(..)
  -- * Operations
  , toFormula
  , natToPoly
  , varToPoly
  , add
  , bigAdd
  , mult
  , bigMult
  , simplify
  ) where

import Prelude hiding ((&&),(||),not)
import qualified Prelude as Prelude
import Qlogic.NatSat
import Qlogic.Formula hiding (simplify)
import Control.Monad
import qualified Control.Monad.State.Lazy as State
import qualified Data.List as List
import Data.Typeable
import qualified Data.Set as Set

data DioVar  = forall a. (DioVarClass a) => DioVar a deriving Typeable
data VPower a  = VPower a Int
               deriving (Eq, Ord, Show, Typeable)
data DioMono a = DioMono Int [VPower a]
               deriving (Eq, Ord, Show, Typeable)
type DioPoly a = [DioMono a]
data DioAtom a = Grt (DioPoly a) (DioPoly a)
               | Equ (DioPoly a) (DioPoly a)
               deriving (Eq, Ord, Show, Typeable)

class PropositionalAtomClass a => DioVarClass a where
  toDioVar :: a -> DioVar
  toDioVar = DioVar
  fromDioVar :: DioVar -> Maybe a
  fromDioVar (DioVar a) = cast a

instance PropositionalAtomClass a => PropositionalAtomClass (DioAtom a)
instance PropositionalAtomClass a => PropositionalAtomClass (DioPoly a)
instance PropositionalAtomClass a => PropositionalAtomClass (DioMono a)
instance PropositionalAtomClass a => PropositionalAtomClass (VPower a)
instance PropositionalAtomClass a => DioVarClass a
type DioFormula a = Formula (DioAtom a)

instance Show DioVar where
  show (DioVar a) = "DioVar " ++ show  a

compareDioVar :: DioVar -> DioVar -> Ordering
DioVar (a :: at) `compareDioVar` DioVar (b :: bt) | ta == tb = (cast a :: Maybe at) `compare` (cast b :: Maybe at)
                                                  | otherwise = show ta `compare` show tb
   where ta = typeOf a
         tb = typeOf b

instance Eq DioVar where
  a == b = {-# SCC "DioVarEq" #-} a `compareDioVar` b == EQ

instance Ord DioVar where
  compare = {-# SCC "DioVarOrd" #-} compareDioVar

instance PropositionalAtomClass DioVar

dioAtom :: PropositionalAtomClass a => DioFormula a -> PropositionalFormula
dioAtom fm = A (PropositionalAtom fm)

polyAtom :: PropositionalAtomClass a => Size -> DioPoly a -> NatFormula
polyAtom n p = natAtom n $ A (PropositionalAtom p)

monoAtom :: PropositionalAtomClass a => Size -> DioMono a -> NatFormula
monoAtom n m = natAtom n $ A (PropositionalAtom m)

powerAtom :: PropositionalAtomClass a => Size -> VPower a -> NatFormula
powerAtom n m = natAtom n $ A (PropositionalAtom m)

data St a = St { vars :: Set.Set a
               , formulas :: Set.Set PropositionalFormula
               , polys :: Set.Set (DioPoly a)
               , monos :: Set.Set (DioMono a)
               , powers :: Set.Set (VPower a)
               }

type DioSetMonad a r = State.State (St a) r

emptySt :: St a
emptySt = St{vars = Set.empty, formulas = Set.empty, polys = Set.empty, monos = Set.empty, powers = Set.empty}

getVars :: DioSetMonad a (Set.Set a)
getForms :: DioSetMonad a (Set.Set PropositionalFormula)
getPolys :: DioSetMonad a (Set.Set (DioPoly a))
getMonos :: DioSetMonad a (Set.Set (DioMono a))
getPowers :: DioSetMonad a (Set.Set (VPower a))

getVars = liftM vars State.get
getForms = liftM formulas State.get
getPolys = liftM polys State.get
getMonos = {-# SCC "getMonos" #-} liftM monos State.get
getPowers = liftM powers State.get

setVars :: Set.Set a -> DioSetMonad a ()
setVars set = State.modify $ \s -> s{vars = set}

setForms :: Set.Set PropositionalFormula -> DioSetMonad a ()
setForms set = State.modify $ \s -> s{formulas = set}

setPolys :: Set.Set (DioPoly a) -> DioSetMonad a ()
setPolys set = State.modify $ \s -> s{polys = set}

setMonos :: Set.Set (DioMono a) -> DioSetMonad a ()
setMonos set = {-# SCC "setMonos" #-} State.modify $ \s -> s{monos = set}

setPowers :: Set.Set (VPower a) -> DioSetMonad a ()
setPowers set = State.modify $ \s -> s{powers = set}

-- maybeComputeForm :: PropositionalAtomClass a
--                  => DioFormula a
--                  -> DioSetMonad a PropositionalFormula
--                  -> DioSetMonad a PropositionalFormula
-- maybeComputeForm fm m =
--   do s <- getForms
--      (if fm `Set.member` s
--       then return (dioAtom fm)
--       else setForms (Set.insert fm s) >> m)

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
 {-# SCC "maybeComputeMono" #-} do s <- getMonos
                                   (if {-# SCC "setmem" #-} fm `Set.member` s
                                    then return (monoAtom n fm)
                                    else setMonos (Set.insert fm s) >> m)

maybeComputePower :: PropositionalAtomClass a
                  => Size
                  -> VPower a
                  -> DioSetMonad a NatFormula
                  -> DioSetMonad a NatFormula
maybeComputePower n fm m =
  do s <- getPowers
     (if fm `Set.member` s
      then return (powerAtom n fm)
      else setPowers (Set.insert fm s) >> m)

toFormGen :: DioVarClass a => (Size -> DioPoly a -> DioSetMonad a NatFormula) -> Size -> DioFormula a -> DioSetMonad a PropositionalFormula
toFormGen f n fm@(A (p `Grt` q)) = do pres <- f n p
                                      qres <- f n q
                                      return $ pres .>. qres
toFormGen f n fm@(A (p `Equ` q)) = do pres <- f n p
                                      qres <- f n q
                                      return $ pres .=. qres
toFormGen f n fm@(And ps)        = do press <- mapM (toFormGen f n) ps
                                      return $ bigAnd press
toFormGen f n fm@(Or ps)         = do press <- mapM (toFormGen f n) ps
                                      return $ bigOr press
toFormGen f n fm@(p `Imp` q)     = do pres <- toFormGen f n p
                                      qres <- toFormGen f n q
                                      return $ pres --> qres
toFormGen f n fm@(p `Iff` q)     = do pres <- toFormGen f n p
                                      qres <- toFormGen f n q
                                      return $ pres <-> qres
toFormGen f n fm@(Ite p q r)     = do pres <- toFormGen f n p
                                      qres <- toFormGen f n q
                                      rres <- toFormGen f n r
                                      return $ ite pres qres rres
toFormGen f n fm@(Neg p)         = do pres <- toFormGen f n p
                                      return $ neg pres
toFormGen _ _ Top                = return Top
toFormGen _ _ Bot                = return Bot

toFormulaGen :: DioVarClass a => (Size -> DioFormula a -> DioSetMonad a PropositionalFormula) -> Size -> DioFormula a -> PropositionalFormula
toFormulaGen f n phi = {-# SCC "toFormulaGen" #-} fst mainResult && varRestricts && extraForms
                       where varRestricts    = bigAnd (Set.map (varRestrict n) (vars (snd mainResult)))
                             extraForms      = (bigAnd . Set.elems . formulas . snd) mainResult
                             varRestrict n v = (natToFormula . (+ 1) . bound) n .>. natAtom n v
                             mainResult      = State.runState (f n phi) emptySt

-- toFormulaSimp :: DioVarClass a => Size -> DioFormula a -> PropositionalFormula
-- -- ^ translates a Diophantine constraint into a propositional formula,
-- --   where variables are instantiated by values between 0 and n.
-- toFormulaSimp = toFormulaGen toFormulaSimp'
--
-- toFormulaSimp' :: DioVarClass a => Size -> DioFormula a -> DioSetMonad a PropositionalFormula
-- toFormulaSimp' = toFormGen polyToNatSimp
--
-- polyToNatSimp :: DioVarClass a => Size -> DioPoly a -> DioSetMonad a NatFormula
-- polyToNatSimp n = pairEmpty . truncBots . bigPlus . map (monoToNatSimp n)
--                   where pairEmpty x = (x, Set.empty)
--
-- monoToNatSimp :: DioVarClass a => Size -> DioMono a -> NatFormula
-- monoToNatSimp n (DioMono m vp) = truncBots $ natToFormula m .*. (bigTimes . map (powerToNatSimp n)) vp
--
-- powerToNatSimp :: DioVarClass a => Size -> VPower a -> NatFormula
-- powerToNatSimp n (VPower v m) | m > 0     = natAtom n v .*. powerToNatSimp n (VPower v (m - 1))
--                               | otherwise = [Top]

-- Optimisation c of Section 5 in the Fuhs-et-al paper
-- prunes all "numbers" to their maximum length based on
-- the assumption that the value of all variables is at most n
toFormula :: DioVarClass a => Size -> DioFormula a -> PropositionalFormula
-- ^ translates a Diophantine constraint into a propositional formula,
--   where variables are instantiated by values between 0 and n.
--   this function tracks the maximum value of all subformulas.
--   the length of all vectors is possibly pruned according to these
--   maximum values
toFormula = toFormulaGen toFormula'

toFormula' :: DioVarClass a => Size -> DioFormula a -> DioSetMonad a PropositionalFormula
toFormula' = {-# SCC "toFormula'" #-} toFormGen polyToNat

polyToNat :: DioVarClass a => Size -> DioPoly a -> DioSetMonad a NatFormula
polyToNat n []        = return [Bot]
polyToNat n fm@(x:xs) = {-# SCC "polyToNat" #-} maybeComputePoly newmax fm $
                        do pres <- monoToNat n x
                           qres <- polyToNat n xs
                           let newform = bigAnd $ zipWith (<->) (polyAtom newmax fm) (truncTo (bits newmax) $ pres .+. qres)
                           s <- getForms
                           setForms $ Set.insert newform s
                           return $ polyAtom newmax fm
                        where newmax  = polyBound n fm

monoToNat :: DioVarClass a => Size -> DioMono a -> DioSetMonad a NatFormula
monoToNat n (DioMono m [])          = return $ natToFormula m
monoToNat n fm@(DioMono m (vp:vps)) = {-# SCC "monoToNat" #-} maybeComputeMono newmax fm $
                                      do pres <- powerToNat n vp
                                         qres <- monoToNat n (DioMono m vps)
                                         let newform = bigAnd $ zipWith (<->) (monoAtom newmax fm) (multres pres qres)
                                         s <- getForms
                                         setForms $ Set.insert newform s
                                         return $ monoAtom newmax fm
                                      where multres ps qs = truncTo (bits newmax) $ ps .*. qs
                                            newmax     = monoBound n fm

powerToNat :: DioVarClass a => Size -> VPower a -> DioSetMonad a NatFormula
powerToNat n fm@(VPower v m) | m > 0  = {-# SCC "powerToNat" #-} maybeComputePower newmax fm $
                                        do vs <- getVars
                                           setVars (Set.insert v vs)
                                           let pres = natAtom n v
                                           qres <- powerToNat n (VPower v (pred m))
                                           let newform = bigAnd $ zipWith (<->) (powerAtom newmax fm) (multres pres qres)
                                           s <- getForms
                                           setForms $ Set.insert newform s
                                           return $ powerAtom newmax fm
                                        where multres ps qs = truncTo (bits newmax) $ ps .*. qs
                                              newmax        = powerBound n fm
powerToNat n (VPower v m) | otherwise = {-# SCC "powerToNatBase" #-} return [Top]

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
-- AS: TODO: Null-Fall in addcoeff
shallowSimp ((DioMono n xs):ms) | otherwise = (DioMono (foldl addcoeff n (fst ys)) xs):(shallowSimp (snd ys))
                                  where ys                       = List.partition (\(DioMono _ xs') -> xs == xs') ms
                                        addcoeff x (DioMono y _) = x + y

simpMono :: Eq a => DioMono a -> DioMono a
simpMono (DioMono n xs) = DioMono n (simpPower xs)

simpPower :: Eq a => [VPower a] -> [VPower a]
simpPower [] = []
simpPower ((VPower v n):xs) | n == 0    = simpPower xs
-- AS: TODO: Null-Fall in addpow
simpPower ((VPower v n):xs) | otherwise = (VPower v (foldl addpow n (fst ys))):(simpPower (snd ys))
                                          where ys                    = List.partition (\(VPower w _) -> v == w) xs
                                                addpow x (VPower _ y) = x + y
