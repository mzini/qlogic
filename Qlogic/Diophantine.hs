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
import Qlogic.SatSolver hiding (add)
import Qlogic.Boolean
import Qlogic.Formula hiding (simplify)
import Qlogic.PropositionalFormula
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

data VPower a  = VPower a Int
               deriving (Eq, Ord, Show, Typeable)

data DioMono a = DioMono Int [VPower a]
               deriving (Eq, Ord, Show, Typeable)

type DioPoly a = [DioMono a]

data DioAtom a = Grt (DioPoly a) (DioPoly a)
               | Equ (DioPoly a) (DioPoly a)
               deriving (Eq, Ord, Show, Typeable)

class PropAtom a => DioVarClass a where
  toDioVar :: a -> DioVar
  toDioVar = DioVar
  fromDioVar :: DioVar -> Maybe a
  fromDioVar (DioVar a) = cast a

instance PropAtom a => DioVarClass a

instance ShowLimit a => ShowLimit (DioAtom a) where
  showlimit n _ | n <= 0 = ""
  showlimit n (Grt a b)  = "Grt " ++ showlimit (n - 1) a ++ showlimit (n - 1) b
  showlimit n (Equ a b)  = "Grt " ++ showlimit (n - 1) a ++ showlimit (n - 1) b

instance ShowLimit a => ShowLimit (DioMono a) where
  showlimit n _ | n <= 0     = ""
  showlimit n (DioMono c vs) = "DioMono " ++ show n ++ " " ++ showlimit n vs

instance ShowLimit a => ShowLimit (VPower a) where
  showlimit n _ | n <= 0   = ""
  showlimit n (VPower a e) = "VPower " ++ showlimit (n - 1) a ++ " " ++ show e

type DioFormula l a = Formula l (DioAtom a) 

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

instance ShowLimit DioVar where
  showlimit n _ | n <= 0 = ""
  showlimit n (DioVar a) = "DioVar " ++ showlimit (n - 1) a

instance PropAtom DioVar

data St l a  = St { vars :: Set.Set a
                  , formulas :: [PropFormula l]
                  , polys :: Map.Map (DioPoly a) (NatFormula l)
                  , monos :: Map.Map (DioMono a) (NatFormula l)
                  , powers :: Map.Map (VPower a) (NatFormula l)
                  }


newtype DioMonad s l a r = DioMonad {runDio :: State.StateT (St l a) (SatSolver s l) r} 
    deriving (Monad, StateClass.MonadState (St l a))

liftD :: Solver s l => SatSolver s l r -> DioMonad s l a r
liftD = DioMonad . lift


emptySt :: St l a
emptySt = St{vars = Set.empty, formulas = [], polys = Map.empty, monos = Map.empty, powers = Map.empty}

runDioMonad :: Solver s l => DioMonad s l a r -> SatSolver s l (r, St l a)
runDioMonad (DioMonad m) = State.runStateT  m emptySt

getVars :: Solver s l => DioMonad s l a (Set.Set a)
getVars = vars `liftM` State.get

getPolys :: Solver s l => DioMonad s l a (Map.Map (DioPoly a) (NatFormula l))
getPolys = polys `liftM` State.get

getMonos :: Solver s l => DioMonad s l a (Map.Map (DioMono a) (NatFormula l))
getMonos = monos `liftM` State.get

getPowers :: Solver s l => DioMonad s l a (Map.Map (VPower a) (NatFormula l))
getPowers = powers `liftM` State.get


setVars :: Solver s l => Set.Set a -> DioMonad s l a ()
setVars set = State.modify $ \s -> s{vars = set}

setPolys :: Solver s l => Map.Map (DioPoly a) (NatFormula l) -> DioMonad s l a ()
setPolys tbl = State.modify $ \s -> s{polys = tbl}

setMonos :: Solver s l => Map.Map (DioMono a) (NatFormula l) -> DioMonad s l a ()
setMonos tbl = State.modify $ \s -> s{monos = tbl}

setPowers :: Solver s l => Map.Map (VPower a) (NatFormula l) -> DioMonad s l a ()
setPowers tbl = State.modify $ \s -> s{powers = tbl}

maybeComputePoly :: (PropAtom a, Solver s l)
                 => Size
                 -> DioPoly a
                 -> DioMonad s l a (NatFormula l)
                 -> DioMonad s l a (NatFormula l)
maybeComputePoly n fm m =
  do s <- getPolys
     (case Map.lookup fm s of
        Just x  -> return x
        Nothing -> do mres <- m
                      setPolys (Map.insert fm mres s)
                      return mres)

maybeComputeMono :: (PropAtom a, Solver s l)
                 => Size
                 -> DioMono a
                 -> DioMonad s l a (NatFormula l)
                 -> DioMonad s l a (NatFormula l)
maybeComputeMono n fm m =
  do s <- getMonos
     (case Map.lookup fm s of
        Just x  -> return x
        Nothing -> do mres <- m
                      setMonos (Map.insert fm mres s)
                      return mres)

maybeComputePower :: (PropAtom a, Solver s l)
                  => Size
                  -> VPower a
                 -> DioMonad s l a (NatFormula l)
                 -> DioMonad s l a (NatFormula l)
maybeComputePower n fm m =
  do s <- getPowers
     (case Map.lookup fm s of
        Just x  -> return x
        Nothing -> do mres <- m
                      setPowers (Map.insert fm mres s)
                      return mres)

toFormGen :: (Eq l, DioVarClass a, Solver s l)
          => (Size -> DioPoly a -> DioMonad s l a (NatFormula l))
          -> Size
          -> DioFormula l a
          -> DioMonad s l a (PropFormula l)
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
                                      return $ not pres
toFormGen _ _ Top                = return Top
toFormGen _ _ Bot                = return Bot

toFormulaGen :: (Eq l, Ord l, DioVarClass a, Solver s l)
             => (Size -> DioFormula l a -> DioMonad s l a (PropFormula l))
             -> Size
             -> DioFormula l a
             -> SatSolver s l (PropFormula l)
toFormulaGen f n phi = 
    do (r,st) <- runDioMonad (f n phi)
       return $ r && varRestricts st && extraForms st
    where varRestricts st = bigAnd (Set.map (varRestrict n) (vars st))
          extraForms st   = bigAnd $ formulas st
          varRestrict n v = (natToFormula . (+ 1) . bound) n .>. natAtom n v


-- Optimisation c of Section 5 in the Fuhs-et-al paper
-- prunes all "numbers" to their maximum length based on
-- the assumption that the value of all variables is at most n
toFormula :: (Ord l, DioVarClass a, Solver s l) => Size -> DioFormula l a -> SatSolver s l (PropFormula l)
-- ^ translates a Diophantine constraint into a propositional formula,
--   where variables are instantiated by values between 0 and n.
--   this function tracks the maximum value of all subformulas.
--   the length of all vectors is possibly pruned according to these
--   maximum values
toFormula = toFormulaGen toFormula'

toFormula' :: (Eq l, Ord l, DioVarClass a, Solver s l) => Size -> DioFormula l a -> DioMonad s l a (PropFormula l)
toFormula' = {-# SCC "toFormula'" #-} toFormGen polyToNat


natComputation :: Solver s l => NatMonad s l (NatFormula l) -> Size -> DioMonad s l a (NatFormula l)
natComputation m b = 
    do (r,fms) <- liftD $ runNatMonad m
       State.modify $ \s -> s{formulas = fms ++ formulas s}
       return $ truncTo (bits b) r

polyToNat :: (Solver s l, DioVarClass a, Ord l) => Size -> DioPoly a -> DioMonad s l a (NatFormula l)
polyToNat n []        = return [Bot]
polyToNat n fm@(x:xs) = {-# SCC "polyToNat" #-} maybeComputePoly newmax fm $
                        do pres <- monoToNat n x
                           qres <- polyToNat n xs
                           natComputation (mAdd pres qres) newmax
    where newmax = polyBound n fm

monoToNat :: (Solver s l, DioVarClass a, Ord l) => Size -> DioMono a -> DioMonad s l a (NatFormula l)
monoToNat n (DioMono m [])          = return $ natToFormula m
monoToNat n fm@(DioMono m (vp:vps)) = {-# SCC "monoToNat" #-} maybeComputeMono newmax fm $
                                      do pres <- powerToNat n vp
                                         qres <- monoToNat n (DioMono m vps)
                                         natComputation (mTimes pres qres) newmax
    where newmax = monoBound n fm

powerToNat :: (Solver s l, DioVarClass a, Ord l) => Size -> VPower a -> DioMonad s l a (NatFormula l)
powerToNat n fm@(VPower v m) | m > 0  = {-# SCC "powerToNat" #-} maybeComputePower newmax fm $
                                        do vs <- getVars
                                           setVars (Set.insert v vs)
                                           let pres = natAtom n v
                                           qres <- powerToNat n (VPower v (pred m))
                                           natComputation (mTimes pres qres) newmax
                             where newmax        = powerBound n fm

powerToNat n (VPower v m) | otherwise = {-# SCC "powerToNatBase" #-} return [Top]

polyBound :: Size -> DioPoly a -> Size
polyBound n = {-# SCC "polyBound" #-} Bound . sum . map (bound . (monoBound n))

monoBound :: Size -> DioMono a -> Size
monoBound n (DioMono m xs) = {-# SCC "monoBound" #-} Bound $ foldr ((*) . bound . powerBound n) m xs

powerBound :: Size -> VPower a -> Size
powerBound n (VPower x m) = {-# SCC "powerBound" #-} Bound $ bound n ^ m

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
shallowSimp ((DioMono n xs):ms) | otherwise = {-# SCC "shallowSimp" #-} (DioMono (foldl addcoeff n (fst ys)) xs):(shallowSimp (snd ys))
                                  where ys                       = List.partition (\(DioMono _ xs') -> xs == xs') ms
                                        addcoeff x (DioMono y _) = x + y

simpMono :: Eq a => DioMono a -> DioMono a
simpMono (DioMono n xs) = DioMono n (simpPower xs)

simpPower :: Eq a => [VPower a] -> [VPower a]
simpPower [] = []
simpPower ((VPower v n):xs) | n == 0    = simpPower xs
-- AS: TODO: Null-Fall in addpow
simpPower ((VPower v n):xs) | otherwise = {-# SCC "simpPower" #-} (VPower v (foldl addpow n (fst ys))):(simpPower (snd ys))
                                          where ys                    = List.partition (\(VPower w _) -> v == w) xs
                                                addpow x (VPower _ y) = x + y


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
