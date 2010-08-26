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

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Qlogic.NatSat
  -- (
  -- -- * Types
  -- NatFormula
  -- , PLVec(..)
  -- , NatAssign
  -- , Size(..)
  -- -- * Operations
  -- , emptyAssignment
  -- , natToFormula
  -- , truncBots
  -- , truncTo
  -- , natToBits
  -- , bitsToNat
  -- , bits
  -- , bound
  -- , mAdd
  -- , (.+.)
  -- , bigPlus
  -- , mTimes
  -- , (.*.)
  -- , bigTimes
  -- , (.>.)
  -- , (.=.)
  -- , natAtom
  -- , natAssignment
  -- , eval
  -- )
where

import Control.Monad
import qualified Control.Monad.State.Class as StateClass
import qualified Control.Monad.State.Lazy as State
import Control.Monad.Trans
import Qlogic.Formula
import Qlogic.SatSolver
import Prelude hiding ((&&), (||), not)
import Qlogic.Boolean
import Qlogic.PropositionalFormula
import qualified Qlogic.Semiring as SR
import qualified Qlogic.Assign as A
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Typeable

type NatFormula l = [PropFormula l]

data Size = Bits Int
          | Bound Int
          deriving (Show, Typeable)

instance SR.Semiring Int where
  plus = (+)
  prod = (*)
  zero = 0
  one = 1

instance Eq Size where
  a == b = bound a == bound b

instance Ord Size where
  compare a b = compare (bound a) (bound b)

natToBits :: Int -> Int
-- ^ calculates the necessary length of a list of Top/Bot values for representing
--   the given natural number
natToBits n | n <= 1    = 1
            | otherwise = succ $ natToBits $ n `div` 2

bitsToNat :: Int -> Int
bitsToNat n = max 0 $ (2 ^ n) - 1

bits :: Size -> Int
bits (Bits n)  = n
bits (Bound n) = natToBits n

bound :: Size -> Int
bound (Bits n) = bitsToNat n
bound (Bound n) = n

increment :: Size -> Size
increment (Bits n)  = Bits $ n + 1
increment (Bound n) = Bound $ 2 * n + 1

data PLVec a = PLVec a Int
  deriving (Eq, Ord, Show, Typeable)

-- instance ShowLimit a => ShowLimit (PLVec a) where
--   showlimit n _ | n <= 0  = ""
--   showlimit n (PLVec a i) = "PLVec " ++ showlimit (n - 1) a ++ show i

instance (Eq a, Ord a, Show a, Typeable a) => PropAtom (PLVec a)

type NatAssign a = Map.Map a Int

emptyAssignment :: NatAssign a
emptyAssignment = Map.empty

natToFormula :: Int -> NatFormula l
-- ^ transforms a natural number into a list of Top/Bot values
natToFormula n | n == 0    = [Bot]
               | n == 1    = [Top]
               | n < 0     = error "Only natural numbers allowed in argument!"
               | otherwise = natToFormula (n `div` 2) ++ natToFormula (n `mod` 2)

newtype NatMonad s l r = NatMonad {runNat :: State.StateT [PropFormula l] (SatSolver s l) r}
    deriving (Monad, StateClass.MonadState [PropFormula l])

liftN :: Solver s l => SatSolver s l r -> NatMonad s l r
liftN = NatMonad . lift

runNatMonad :: NatMonad s l r -> SatSolver s l (r, [PropFormula l])
runNatMonad (NatMonad m) = State.runStateT m []

toFormula :: (Eq l, Monad s) =>  NatMonad s l (PropFormula l) -> SatSolver s l (PropFormula l)
toFormula m = do (r,fms) <- runNatMonad m
                 return $ bigAnd (r : fms)

freshVar :: Solver s l => NatMonad s l (PropFormula l)
freshVar = literal `liftM` liftN freshLit

enforce :: Solver s l => [PropFormula l] -> NatMonad s l ()
enforce f = State.modify (f ++)

maybeFreshVar :: (Eq l, Solver s l) => NatMonad s l (PropFormula l) -> NatMonad s l (PropFormula l)
maybeFreshVar mf = mf >>= f
  where f Top      = return Top
        f Bot      = return Bot
        f a@(SL _) = return a
        f a@(A _)  = return a
        f fml      = do c <- freshVar
                        enforce [c <-> fml]
                        return c

instance (Solver s l, Boolean r) => Boolean (NatMonad s l r) where
  (&&) = liftM2 (&&)
  (||) = liftM2 (||)
  not = liftM not
  top = return top
  bot = return bot
  (<->) = liftM2 (<->)
  (-->) = liftM2 (-->)
  ite = liftM3 ite

truncBots :: NatFormula l -> NatFormula l
-- ^ removes leading Bottoms from a list of propositional formulas
--   however, the last Bot in a list consisting only of Bots is never removed
truncBots []       = []
truncBots f@[_]    = f
truncBots (Bot:ps) = truncBots ps
truncBots f@(_:_)  = f

truncTo :: Int -> NatFormula l -> NatFormula l
-- ^ If the given list of propositional formulas is longer than n, its length is reduced
--   to n by chopping off the first elements
truncTo _ []                         = []
truncTo n qs@(_:ps) | length qs <= n = qs
                    | otherwise      = truncTo n ps

mTruncTo :: (Ord l, Solver s l) => Int -> NatFormula l -> NatMonad s l (NatFormula l)
mTruncTo _ []                         = return []
mTruncTo n qs@(p:ps) | length qs <= n = return qs
                     | otherwise      = do enforce [not p]
                                           mTruncTo n ps

padBots :: Int -> NatFormula l -> NatFormula l
padBots n | n == 0    = id
          | n > 0     = (Bot :) . padBots (n - 1)
          | otherwise = error "Only natural numbers allowed in argument!"

mAdd :: (Ord l, Solver s l) => NatFormula l -> NatFormula l -> NatMonad s l (NatFormula l)
-- MA:TODO: l ist nicht typeable, was tun?
mAdd [] []                  = return []
mAdd [p] [q]                = do c1 <- maybeFreshVar $ return $ p && q
                                 c2 <- maybeFreshVar $ return $ not (p <-> q)
                                 return [c1, c2]
mAdd ps qs | lengthdiff > 0 = mAdd (padBots lengthdiff ps) qs
           | lengthdiff < 0 = mAdd qs ps
           | otherwise      = do rs <- mAdd (tail ps) (tail qs)
                                 let r = head rs
                                 c1 <- maybeFreshVar $ return $ twoOrThree p q r
                                 c2 <- maybeFreshVar $ return $ oneOrThree p q r
                                 return $ c1 : c2 : tail rs
  where lengthdiff  = length qs - length ps
        p           = head ps
        q           = head qs

mTimes :: (Ord l, Solver s l) => NatFormula l -> NatFormula l -> NatMonad s l (NatFormula l)
mTimes _ []      = return []
mTimes [] _      = return []
mTimes ps [q]    = do return $ map (&& q) ps
mTimes [p] qs    = mTimes qs [p]
mTimes ps (q:qs) = do let r1 = map (&& q) ps ++ padBots (length qs) []
                      r2 <- mTimes ps qs
                      addres <- mAdd r1 r2
                      vs <- mapM (maybeFreshVar . return) addres
                      return vs

mGrt :: (Solver s l, Eq l) => NatFormula l -> NatFormula l -> NatMonad s l (PropFormula l)
[] `mGrt` []                  = return Bot
[p] `mGrt` [q]                = return $ p && not q
ps `mGrt` qs | lengthdiff > 0 = padBots lengthdiff ps `mGrt` qs
             | lengthdiff < 0 = ps `mGrt` padBots (abs lengthdiff) qs
             | otherwise      = do subresult <- tail ps `mGrt` tail qs
                                   return $ (p && not q) || ((q --> p) && subresult)
   where lengthdiff        = length qs - length ps
         p                 = head ps
         q                 = head qs

mGeq :: (Solver s l, Eq l) => NatFormula l -> NatFormula l -> NatMonad s l (PropFormula l)
[] `mGeq` []                  = return Top
[p] `mGeq` [q]                = return $ p || not q
ps `mGeq` qs | lengthdiff > 0 = padBots lengthdiff ps `mGeq` qs
             | lengthdiff < 0 = ps `mGeq` padBots (abs lengthdiff) qs
             | otherwise      = do subresult <- tail ps `mGeq` tail qs
                                   return $ (p && not q) || ((q --> p) && subresult)
   where lengthdiff = length qs - length ps
         p          = head ps
         q          = head qs

mEqu :: (Solver s l, Eq l) => NatFormula l -> NatFormula l -> NatMonad s l (PropFormula l)
-- ^ performs equality comparisons of integers in the representation
--   as a list of propositional formulas
[] `mEqu` []                  = return Top
[p] `mEqu` [q]                = return $ p <-> q
ps `mEqu` qs | lengthdiff > 0 = padBots lengthdiff ps `mEqu` qs
             | lengthdiff < 0 = ps `mEqu` padBots (abs lengthdiff) qs
             | otherwise      = do subresult <- tail ps `mEqu` tail qs
                                   return $ (head ps <-> head qs) && subresult
   where lengthdiff = length qs - length ps

-- creates a variable with enough bits to represent n
natAtom :: (PropAtom a, Eq l) => Size -> a -> NatFormula l
-- ^ creates a "natural number variable" encoded by a list of
--   propositional variables. The length of the list is chosen
--   to be exactly enough in order to represent n
natAtom sz a = nBitVar (bits sz) a

natAtomM :: (PropAtom a, Eq l, Solver s l) => Size -> a -> NatMonad s l (NatFormula l)
natAtomM sz a = do let v = nBitVar (bits sz) a
                   varRestrict <- natToFormula (bound sz) `mGeq` v
                   enforce [varRestrict]
                   return v

nBitVar :: (PropAtom a, Eq l) => Int -> a -> NatFormula l
nBitVar n v = nBitVar' 1 n v

-- unsafePerformIO $ do putStrLn $ "nBitVar (" ++ show i ++ ") (" ++ show n ++ ") (" ++ show v ++ ")"
--                                                   return $ 

nBitVar' :: (PropAtom a, Eq l) => Int -> Int -> a -> NatFormula l
nBitVar' i n v | i <= n    = propAtom (PLVec v i) : nBitVar' (i + 1) n v
               | otherwise = []

baseFromVec :: (Ord a, Show a, Typeable a) => PLVec a -> a
baseFromVec (PLVec x _) = x

-- varRestrict :: (PropAtom a, Eq l) => Int -> a -> PropFormula l
-- varRestrict n v = natToFormula n .>=. nBitVar (natToBits n) v

natAssignment :: (Ord a, Typeable a) => Size -> A.Assign () -> NatAssign a
natAssignment s = Map.foldWithKey f Map.empty
  where f _        False natAss       = natAss
        f (Right (PA k)) True  natAss =
            case cast k of 
              Just (PLVec var i) -> Map.alter (modifyBit i) var natAss
              Nothing            -> natAss
        modifyBit i (Just n)                 = Just $ n + 2^(bts - i)
        modifyBit i Nothing                  = Just $ 2^(bts - i)
        bts = bits s

eval ::  Ord l => NatFormula l -> A.Assign l -> Int
eval f ass = boolsToNat $ map (flip A.eval ass) f

boolsToNat :: [Bool] -> Int
boolsToNat = List.foldl' f 0
             where f n True = 2 * n + 1
                   f n False = 2 * n
