{-
This file is part of the Haskell Qlogic Library.

The Haskell Qlogic Library is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

The Haskell Qlogic Library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with the Haskell Qlogic Library.  If not, see <http://www.gnu.org/licenses/>.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

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
  , MSemiring(..)
  , SizeSemiring(..)
  -- * Operations
  , toFormula
  , constToPoly
  , varToPoly
  , restrictVarToPoly
  , add
  , bigAdd
  , mult
  , bigMult
  , simplify
  ) where

import Prelude hiding ((&&),(||),not)
import qualified Prelude as Prelude
import qualified Qlogic.Arctic as A
import qualified Qlogic.ArcSat as AS
import qualified Qlogic.NatSat as N
import Qlogic.SatSolver hiding (add)
import Qlogic.Boolean hiding (fm)
import Qlogic.Formula hiding (simplify)
import Qlogic.PropositionalFormula
import qualified Qlogic.Semiring as SR
import Control.Monad
import Control.Monad.Trans (lift)
import qualified Control.Monad.State.Lazy as State
import qualified Control.Monad.State.Class as StateClass
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Typeable
import qualified Data.Set as Set
import Qlogic.Utils

data DioVar  = forall a. (DioVarClass a) => DioVar a deriving Typeable

data VPower a = VPower a Int | RestrictVar a Int
  deriving (Eq, Ord, Show, Typeable)

data DioMono a b = DioMono b [VPower a]
  deriving (Eq, Ord, Show, Typeable)

type DioPoly a b = [DioMono a b]

data DioAtom a b = Grt (DioPoly a b) (DioPoly a b)
                 | Geq (DioPoly a b) (DioPoly a b)
                 | Equ (DioPoly a b) (DioPoly a b)
                 | PAtom a
                 deriving (Eq, Ord, Show, Typeable)

class (Solver s l, SizeSemiring b) => MSemiring s l f a b | f -> a, f -> b, f -> s, f -> l, b -> f where
  plus :: f -> f -> N.NatMonad s l f
  plus x y = bigPlus [x, y]
  prod :: f -> f -> N.NatMonad s l f
  prod x y = bigProd [x, y]
  zero :: f
  one :: f
  geq :: f -> f -> N.NatMonad s l (PropFormula l)
  grt :: f -> f -> N.NatMonad s l (PropFormula l)
  equ :: f -> f -> N.NatMonad s l (PropFormula l)
  constToFormula :: b -> f
  formAtom :: b -> a -> N.NatMonad s l f
  truncFormTo :: Int -> f -> N.NatMonad s l f
  bigPlus :: [f] -> N.NatMonad s l f
  bigPlus = foldM plus zero
  bigProd :: [f] -> N.NatMonad s l f
  bigProd = foldM prod one

class SR.Semiring b => SizeSemiring b where
  sizeToBits :: b -> Int
  bitsToSize :: Int -> b

instance SizeSemiring Int where
  sizeToBits n = N.bits $ N.Bound n
  bitsToSize n = N.bound $ N.Bits n

instance SizeSemiring A.ArcInt where
  sizeToBits = AS.arcToBits
  bitsToSize = AS.bitsToArc

class PropAtom a => DioVarClass a where
  toDioVar :: a -> DioVar
  toDioVar = DioVar
  fromDioVar :: DioVar -> Maybe a
  fromDioVar (DioVar a) = cast a

instance PropAtom a => DioVarClass a

-- instance ShowLimit a => ShowLimit (DioAtom a) where
--   showlimit n _ | n <= 0 = ""
--   showlimit n (Grt a b)  = "Grt " ++ showlimit (n - 1) a ++ showlimit (n - 1) b
--   showlimit n (Equ a b)  = "Grt " ++ showlimit (n - 1) a ++ showlimit (n - 1) b

-- instance ShowLimit a => ShowLimit (DioMono a) where
--   showlimit n _ | n <= 0     = ""
--   showlimit n (DioMono c vs) = "DioMono " ++ show n ++ " " ++ showlimit n vs

-- instance ShowLimit a => ShowLimit (VPower a) where
--   showlimit n _ | n <= 0   = ""
--   showlimit n (VPower a e) = "VPower " ++ showlimit (n - 1) a ++ " " ++ show e

type DioFormula l a b = Formula l (DioAtom a b)

instance Show DioVar where
  show (DioVar a) = "DioVar (" ++ show a ++ ")"

compareDioVar :: DioVar -> DioVar -> Ordering
DioVar (a :: at) `compareDioVar` DioVar (b :: bt) | ta == tb = (cast a :: Maybe at) `compare` (cast b :: Maybe at)
                                                  | otherwise = show ta `compare` show tb
   where ta = typeOf a
         tb = typeOf b

instance Eq DioVar where
  a == b = a `compareDioVar` b == EQ

instance Ord DioVar where
  compare = compareDioVar

-- instance ShowLimit DioVar where
--   showlimit n _ | n <= 0 = ""
--   showlimit n (DioVar a) = "DioVar " ++ showlimit (n - 1) a

instance PropAtom DioVar

data St l a b f = St { vars :: Set.Set a
                     , formulas :: [PropFormula l]
                     , polys :: Map.Map (DioPoly a b) f
                     , monos :: Map.Map (DioMono a b) f
                     , powers :: Map.Map (VPower a) f
                     }


newtype DioMonad s l a b f r = DioMonad {runDio :: State.StateT (St l a b f) (SatSolver s l) r}
    deriving (Monad, StateClass.MonadState (St l a b f))

liftD :: MSemiring s l f a b => SatSolver s l r -> DioMonad s l a b f r
liftD = DioMonad . lift


emptySt :: St l a b f
emptySt = St{vars = Set.empty, formulas = [], polys = Map.empty, monos = Map.empty, powers = Map.empty}

runDioMonad :: Solver s l => DioMonad s l a b f r -> SatSolver s l (r, St l a b f)
runDioMonad (DioMonad m) = State.runStateT m emptySt

getVars :: MSemiring s l f a b => DioMonad s l a b f (Set.Set a)
getVars = vars `liftM` State.get

getPolys :: MSemiring s l f a b => DioMonad s l a b f (Map.Map (DioPoly a b) f)
getPolys = polys `liftM` State.get

getMonos :: MSemiring s l f a b => DioMonad s l a b f (Map.Map (DioMono a b) f)
getMonos = monos `liftM` State.get

getPowers :: MSemiring s l f a b => DioMonad s l a b f (Map.Map (VPower a) f)
getPowers = powers `liftM` State.get


setVars :: MSemiring s l f a b => Set.Set a -> DioMonad s l a b f ()
setVars set = State.modify $ \s -> s{vars = set}

setPolys :: MSemiring s l f a b => Map.Map (DioPoly a b) f -> DioMonad s l a b f ()
setPolys tbl = State.modify $ \s -> s{polys = tbl}

setMonos :: MSemiring s l f a b => Map.Map (DioMono a b) f -> DioMonad s l a b f ()
setMonos tbl = State.modify $ \s -> s{monos = tbl}

setPowers :: MSemiring s l f a b => Map.Map (VPower a) f -> DioMonad s l a b f ()
setPowers tbl = State.modify $ \s -> s{powers = tbl}

maybeComputePoly :: (PropAtom a, Ord b, MSemiring s l f a b)
                 => DioPoly a b
                 -> DioMonad s l a b f f
                 -> DioMonad s l a b f f
maybeComputePoly fm m =
  do s <- getPolys
     (case Map.lookup fm s of
        Just x  -> return x
        Nothing -> do mres <- m
                      setPolys (Map.insert fm mres s)
                      return mres)

maybeComputeMono :: (PropAtom a, Ord b, MSemiring s l f a b)
                 => DioMono a b
                 -> DioMonad s l a b f f
                 -> DioMonad s l a b f f
maybeComputeMono fm m =
  do s <- getMonos
     (case Map.lookup fm s of
        Just x  -> return x
        Nothing -> do mres <- m
                      setMonos (Map.insert fm mres s)
                      return mres)

maybeComputePower :: (PropAtom a, Ord b, MSemiring s l f a b)
                  => VPower a
                  -> DioMonad s l a b f f
                  -> DioMonad s l a b f f
maybeComputePower fm m =
  do s <- getPowers
     (case Map.lookup fm s of
        Just x  -> return x
        Nothing -> do mres <- m
                      setPowers (Map.insert fm mres s)
                      return mres)

toFormGen :: (Eq l, DioVarClass a, MSemiring s l f a b)
          => (Maybe b -> b -> DioPoly a b -> DioMonad s l a b f f)
          -> Maybe b
          -> b
          -> DioFormula l a b
          -> DioMonad s l a b f (PropFormula l)
toFormGen f cb n (A (p `Grt` q)) = do pres <- f cb n p
                                      qres <- f cb n q
                                      natComputation $ pres `grt` qres
toFormGen f cb n (A (p `Geq` q)) = do pres <- f cb n p
                                      qres <- f cb n q
                                      natComputation $ pres `geq` qres
toFormGen f cb n (A (p `Equ` q)) = do pres <- f cb n p
                                      qres <- f cb n q
                                      natComputation $ pres `equ` qres
toFormGen f cb n (A (PAtom p))   = return $ propAtom p 
toFormGen f cb n (And ps)        = do press <- mapM (toFormGen f cb n) ps
                                      return $ bigAnd press
toFormGen f cb n (Or ps)         = do press <- mapM (toFormGen f cb n) ps
                                      return $ bigOr press
toFormGen f cb n (p `Imp` q)     = do pres <- toFormGen f cb n p
                                      qres <- toFormGen f cb n q
                                      return $ pres --> qres
toFormGen f cb n (p `Iff` q)     = do pres <- toFormGen f cb n p
                                      qres <- toFormGen f cb n q
                                      return $ pres <-> qres
toFormGen f cb n (Ite p q r)     = do pres <- toFormGen f cb n p
                                      qres <- toFormGen f cb n q
                                      rres <- toFormGen f cb n r
                                      return $ ite pres qres rres
toFormGen f cb n (Neg p)         = do pres <- toFormGen f cb n p
                                      return $ not pres
toFormGen _ _ _ Top                = return Top
toFormGen _ _ _ Bot                = return Bot

toFormulaGen :: (Ord l, DioVarClass a, MSemiring s l f a b)
             => (Maybe b -> b -> DioFormula l a b -> DioMonad s l a b f (PropFormula l))
             -> Maybe b
             -> b
             -> DioFormula l a b
             -> SatSolver s l (PropFormula l)
toFormulaGen f cb n phi =
    do (r,st) <- runDioMonad (f cb n phi)
       return $ r && bigAnd (formulas st)

-- Optimisation c of Section 5 in the Fuhs-et-al paper
-- prunes all "numbers" to their maximum length based on
-- the assumption that the value of all variables is at most n
toFormula :: (Ord l, Ord b, DioVarClass a, MSemiring s l f a b) => Maybe b -> b -> DioFormula l a b -> SatSolver s l (PropFormula l)
-- ^ translates a Diophantine constraint into a propositional formula,
--   where variables are instantiated by values between 0 and n.
--   this function tracks the maximum value of all subformulas.
--   the length of all vectors is possibly pruned according to these
--   maximum values
toFormula = toFormulaGen toFormula'

toFormula' :: (Eq l, Ord l, Ord b, DioVarClass a, MSemiring s l f a b) => Maybe b -> b -> DioFormula l a b -> DioMonad s l a b f (PropFormula l)
toFormula' = toFormGen polyToNat

natComputation :: MSemiring s l f a b => N.NatMonad s l g -> DioMonad s l a b f g
natComputation m =
    do (r,fms) <- liftD $ N.runNatMonad m
       State.modify $ \s -> s{formulas = fms ++ formulas s}
       return r

natComputation_ :: MSemiring s l f a b => N.NatMonad s l f -> Maybe b -> b -> DioMonad s l a b f f
natComputation_ m cb b =
    do r <- natComputation m
       case cb of
         Nothing -> natComputation $ truncFormTo (sizeToBits b) r
         Just b' -> natComputation $ truncFormTo (min (sizeToBits b') (sizeToBits b)) r

polyToNat :: (MSemiring s l f a b, DioVarClass a, Ord l, Ord b) => Maybe b -> b -> DioPoly a b -> DioMonad s l a b f f
polyToNat cb n []        = return zero
polyToNat cb n [x]       = monoToNat cb n x
polyToNat cb n fm@(x:xs) = maybeComputePoly fm $
                           do pres <- monoToNat cb n x
                              qres <- polyToNat cb n xs
                              natComputation_ (plus pres qres) cb newmax
    where newmax = polyBound n fm

monoToNat :: (MSemiring s l f a b, DioVarClass a, Ord l, Ord b) => Maybe b -> b -> DioMono a b -> DioMonad s l a b f f
monoToNat cb n (DioMono m [])          = return $ constToFormula m
monoToNat cb n fm@(DioMono m (vp:vps)) = maybeComputeMono fm $
                                         do pres <- powerToNat cb n vp
                                            qres <- monoToNat cb n (DioMono m vps)
                                            natComputation_ (prod pres qres) cb newmax
    where newmax = monoBound n fm

powerToNat :: (MSemiring s l f a b, DioVarClass a, Ord l, Ord b) => Maybe b -> b -> VPower a -> DioMonad s l a b f f
powerToNat cb n fm@(VPower v m) | m > 1  = maybeComputePower fm $
                                           do State.modify (\s -> s{vars = Set.insert v $ vars s})
                                              pres <- powerToNat cb n (VPower v 1)
                                              qres <- powerToNat cb n (VPower v (pred m))
                                              natComputation_ (prod pres qres) cb newmax
                    where newmax = powerBound n fm
powerToNat cb n fm@(VPower v m) | m == 1 = maybeComputePower fm $ natComputation_ (formAtom n v) cb n
powerToNat cb n (VPower v m) | otherwise = return one
powerToNat cb n fm@(RestrictVar v m) | m > 1  = maybeComputePower fm $
                                        do State.modify (\s -> s{vars = Set.insert v $ vars s})
                                           pres <- powerToNat cb n (RestrictVar v 1)
                                           qres <- powerToNat cb n (RestrictVar v (pred m))
                                           natComputation_ (prod pres qres) cb newmax
                    where newmax = powerBound n fm
powerToNat cb n fm@(RestrictVar v m) | m == 1    = maybeComputePower fm $ natComputation_ (formAtom SR.one v) cb n
                                     | otherwise = return one

polyBound :: SR.Semiring b => b -> DioPoly a b -> b
polyBound n = SR.bigPlus . map (monoBound n)

monoBound :: SR.Semiring b => b -> DioMono a b -> b
monoBound n (DioMono m xs) = foldr (SR.prod . powerBound n) m xs

powerBound :: SR.Semiring b => b -> VPower a -> b
powerBound n (VPower _ m) = SR.bigProd $ replicate m n
powerBound _ (RestrictVar _ _) = SR.one

constToPoly :: b -> DioPoly a b
constToPoly n = [DioMono n []]

varToPoly :: SR.Semiring b => a -> DioPoly a b
varToPoly v = [DioMono SR.one [VPower v 1]]

restrictVarToPoly :: SR.Semiring b => a -> DioPoly a b
restrictVarToPoly v = [DioMono SR.one [RestrictVar v 1]]

add :: (Eq a, Eq b, SR.Semiring b) => DioPoly a b -> DioPoly a b -> DioPoly a b
add p = shallowSimp . (++) p

bigAdd :: (Eq a, Eq b, SR.Semiring b) => [DioPoly a b] -> DioPoly a b
bigAdd = shallowSimp . concat

mult :: (Eq a, Eq b, SR.Semiring b) => DioPoly a b -> DioPoly a b -> DioPoly a b
mult p = bigAdd . map (pmmult p)

pmmult :: (Eq a, SR.Semiring b) => DioPoly a b -> DioMono a b -> DioPoly a b
pmmult p m = map (mmult m) p

mmult :: (Eq a, SR.Semiring b) => DioMono a b -> DioMono a b -> DioMono a b
mmult (DioMono m xs) (DioMono n ys) = simpMono $ DioMono (m `SR.prod` n) (xs ++ ys)

bigMult :: (Eq a, Eq b, SR.Semiring b) => [DioPoly a b] -> DioPoly a b
bigMult = foldr mult $ constToPoly SR.one

simplify :: (Eq a, Eq b, SR.Semiring b) => DioPoly a b -> DioPoly a b
simplify = shallowSimp . map simpMono

shallowSimp :: (Eq a, Eq b, SR.Semiring b) => DioPoly a b -> DioPoly a b
shallowSimp [] = []
shallowSimp ((DioMono n xs):ms) | n == SR.zero = shallowSimp ms
shallowSimp ((DioMono n xs):ms) | otherwise    = (DioMono (foldl addcoeff n xss) xs):(shallowSimp yss)
                                  where (xss, yss)               = List.partition (\(DioMono _ xs') -> xs == xs') ms
                                        addcoeff x (DioMono y _) = x `SR.plus` y

simpMono :: Eq a => DioMono a b -> DioMono a b
simpMono (DioMono n xs) = DioMono n (simpPower xs)

simpPower :: Eq a => [VPower a] -> [VPower a]
simpPower [] = []
simpPower ((VPower v n):xs) | n == 0    = simpPower xs
simpPower ((VPower v n):xs) | otherwise = (VPower v (foldl addpow n xss)):(simpPower yss)
                                          where (xss, yss)              = List.partition isRightPow xs
                                                isRightPow (VPower w _) = v == w
                                                isRightPow _            = False
                                                addpow x (VPower _ y)   = x `SR.plus` y
simpPower ((RestrictVar v n):xs) | n == 0    = simpPower xs
simpPower ((RestrictVar v n):xs) | otherwise = (RestrictVar v (foldl addpow n xss)):(simpPower yss)
                                          where (xss, yss)                   = List.partition isRightPow xs
                                                isRightPow (RestrictVar w _) = v == w
                                                isRightPow _                 = False
                                                addpow x (RestrictVar _ y)   = x `SR.plus` y


-- toFormulaSimp :: DioVarClass a => Size -> DioFormula l a -> PropFormula
-- -- ^ translates a Diophantine constraint into a propositional formula,
-- --   where variables are instantiated by values between 0 and n.
-- toFormulaSimp = toFormulaGen toFormulaSimp'
--
-- toFormulaSimp' :: DioVarClass a => Size -> DioFormula l a -> DioMonad s a PropFormula
-- toFormulaSimp' = toFormGen polyToNatSimp
--
-- polyToNatSimp :: DioVarClass a => Size -> DioPoly a -> DioMonad s l a NatFormula
-- polyToNatSimp n = pairEmpty . truncBots . bigPlus . map (monoToNatSimp n)
--                   where pairEmpty x = (x, Set.empty)
--
-- monoToNatSimp :: DioVarClass a => Size -> DioMono a -> NatFormula
-- monoToNatSimp n (DioMono m vp) = truncBots $ natToFormula m .*. (bigTimes . map (powerToNatSimp n)) vp
--
-- powerToNatSimp :: DioVarClass a => Size -> VPower a -> NatFormula
-- powerToNatSimp n (VPower v m) | m > 0     = natAtom n v .*. powerToNatSimp n (VPower v (m - 1))
--                               | otherwise = [Top]
