{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Qlogic.IntSat
  -- (
  -- -- * Types
  -- N.NatFormula
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
import qualified Qlogic.NatSat as N
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable
import Qlogic.Utils

data Size = Bits Int
          | Bound Int Int
          deriving (Show, Typeable)

instance Eq Size where
  a == b = bound a == bound b

instance Ord Size where
  compare a b = case compare a'' b'' of
                  LT -> LT
                  GT -> GT
                  EQ -> compare a' b'
                where (a', a'') = bound a
                      (b', b'') = bound b

intToBits :: Int -> Int
-- ^ calculates the necessary length of a list of Top/Bot values for representing
--   the given integer
intToBits n | n < 0     = intToBits $ abs $ n + 1
            | n == 0    = 1
            | n == 1    = 2
            | otherwise = succ $ intToBits $ n `div` 2

signedBitsToNat :: Int -> Int
signedBitsToNat n = (2 ^ (n - 1)) - 1

bits (Bits n)  = n
bits (Bound m n) = max (intToBits m) (intToBits n)

bound (Bits n) = (-(k + 1), k)
  where k = signedBitsToNat n
bound (Bound m n) = (m, n)

lowerbound = fst . bound
upperbound = snd . bound

increment :: Size -> Size
increment (Bits n)    = Bits $ n + 1
increment (Bound m n) = Bound (2 * m) $ 2 * n + 1

twoComplement :: Eq l => Int -> N.NatFormula l
twoComplement n | n == -1   = [Top]
                | n == 0    = [Bot]
                | n >= 1    = Bot : N.natToFormula n
                | otherwise = Top : (map not $ N.natToFormula $ abs n - 1)

truncFront :: Eq l => N.NatFormula l -> N.NatFormula l
truncFront xs | length xs < 2 = xs
              | otherwise     = if x1 == x2 then truncFront (x1 : xs') else xs
                                where x1  = head xs
                                      x2  = head $ tail xs
                                      xs' = tail $ tail xs

truncTo :: Int -> N.NatFormula l -> N.NatFormula l
truncTo n xs | length xs <= Prelude.max 1 n = xs
             | otherwise                    = truncTo n $ tail xs

-- AS: TODO: keine frische Variable für sehr simple (head xs) Fälle
padFrontM :: (Eq l, Solver s l) => Int -> N.NatFormula l -> N.NatMonad s l (N.NatFormula l)
padFrontM n xs | n == 0    = return xs
               | n > 0     = if null xs then return $ replicate n Bot else
                             do c <- N.maybeFreshVar $ return $ head xs
                                return $ replicate n c ++ (c : tail xs)
               | otherwise = error "IntSat.padFrontM: Only natural numbers allowed in argument!"

mNegate :: (Ord l, Solver s l) => N.NatFormula l -> N.NatMonad s l (N.NatFormula l)
mNegate ps = do ps' <- padFrontM 1 ps
                let ps'' = map not ps'
                mAdd ps'' $ twoComplement 1

mAdd :: (Ord l, Solver s l) => N.NatFormula l -> N.NatFormula l -> N.NatMonad s l (N.NatFormula l)
-- MA:TODO: l ist nicht typeable, was tun?
mAdd [] []                  = return []
mAdd [p] [q]                = do c1 <- N.maybeFreshVar $ return $ p || q
                                 c2 <- N.maybeFreshVar $ return $ not (p <-> q)
                                 return [c1, c2]
mAdd ps qs | lengthdiff > 0 = do ps' <- padFrontM lengthdiff ps
                                 mAdd ps' qs
           | lengthdiff < 0 = mAdd qs ps
           | otherwise      = do rs <- N.mAdd (tail ps) (tail qs)
                                 let r = head rs
                                 c1 <- N.maybeFreshVar $ return $ (p || q) && (r --> (p && q))
                                 c2 <- N.maybeFreshVar $ return $ oneOrThree p q r
                                 return $ c1 : c2 : tail rs
  where lengthdiff  = length qs - length ps
        p           = head ps
        q           = head qs

mTimes :: (Ord l, Solver s l) => N.NatFormula l -> N.NatFormula l -> N.NatMonad s l (N.NatFormula l)
mTimes _ []      = return []
mTimes [] _      = return []
mTimes ps [q]    = do ps' <- mNegate ps
                      return $ map (&& q) ps'
mTimes [p] qs    = mTimes qs [p]
mTimes ps (q:qs) = do ps' <- mNegate ps
                      let r1 = map (&& q) ps' ++ N.padBots (length qs) []
                      r2 <- unsignedMTimes ps qs
                      addres <- mAdd r1 r2
                      vs <- mapM (N.maybeFreshVar . return) $ tail addres
                      return vs

-- Version of mTimes where the second argument is assumend to be unsigned
unsignedMTimes :: (Ord l, Solver s l) => N.NatFormula l -> N.NatFormula l -> N.NatMonad s l (N.NatFormula l)
unsignedMTimes _ []      = return []
unsignedMTimes [] _      = return []
unsignedMTimes ps [q]    = do return $ map (&& q) ps
unsignedMTimes [p] qs    = unsignedMTimes qs [p]
unsignedMTimes ps (q:qs) = do let r1 = map (&& q) ps ++ N.padBots (length qs) []
                              r2 <- unsignedMTimes ps qs
                              addres <- mAdd r1 r2
                              vs <- mapM (N.maybeFreshVar . return) addres
                              return vs

mGrt :: (Solver s l, Eq l) => N.NatFormula l -> N.NatFormula l -> N.NatMonad s l (PropFormula l)
-- ^ performs "greater than" comparisons of integers in the representation
--   as a list of propositional formulas
[] `mGrt` []                  = return Bot
[p] `mGrt` [q]                = return $ q && not p
ps `mGrt` qs | lengthdiff > 0 = do ps' <- padFrontM lengthdiff ps
                                   ps' `mGrt` qs
             | lengthdiff < 0 = do qs' <- padFrontM (abs lengthdiff) qs
                                   ps `mGrt` qs'
             | otherwise      = do subresult <- tail ps `N.mGrt` tail qs
                                   return $ (not p && q) || ((p --> q) && subresult)
   where lengthdiff = length qs - length ps
         p          = head ps
         q          = head qs

mGeq :: (Solver s l, Eq l) => N.NatFormula l -> N.NatFormula l -> N.NatMonad s l (PropFormula l)
-- ^ performs "greater or equal" comparisons of integers in the representation
--   as a list of propositional formulas
[] `mGeq` []                  = return Top
[p] `mGeq` [q]                = return $ q || not p
ps `mGeq` qs | lengthdiff > 0 = do ps' <- padFrontM lengthdiff ps
                                   ps' `mGeq` qs
             | lengthdiff < 0 = do qs' <- padFrontM (abs lengthdiff) qs
                                   ps `mGeq` qs'
             | otherwise      = do subresult <- tail ps `N.mGeq` tail qs
                                   return $ (not p && q) || ((p --> q) && subresult)
   where lengthdiff = length qs - length ps
         p          = head ps
         q          = head qs

mEqu :: (Solver s l, Eq l) => N.NatFormula l -> N.NatFormula l -> N.NatMonad s l (PropFormula l)
-- ^ performs equality comparisons of integers in the representation
--   as a list of propositional formulas
[] `mEqu` []                  = return Top
[p] `mEqu` [q]                = return $ p <-> q
ps `mEqu` qs | lengthdiff > 0 = do ps' <- padFrontM lengthdiff ps
                                   ps' `mEqu` qs
             | lengthdiff < 0 = do qs' <- padFrontM (abs lengthdiff) qs
                                   ps `mEqu` qs'
             | otherwise      = do subresult <- tail ps `mEqu` tail qs
                                   return $ (head ps <-> head qs) && subresult
   where lengthdiff = length qs - length ps

natAtomM :: (PropAtom a, Eq l, Solver s l) => Size -> a -> N.NatMonad s l (N.NatFormula l)
natAtomM size a = do let v = N.nBitVar (bits size) a
                     lb <- v `mGeq` twoComplement (upperbound size)
                     ub <- twoComplement (upperbound size) `mGeq` v
                     N.enforce [lb, ub]
                     return v

intAssignment :: (Ord a, Typeable a) => Size -> A.Assign () -> N.NatAssign a
intAssignment s = Map.foldWithKey f Map.empty
  where f _        False natAss       = natAss
        f (Right (PA k)) True  natAss =
            case cast k of 
              Just (N.PLVec var i) -> Map.alter (modifyBit i) var natAss
              Nothing              -> natAss
        modifyBit i (Just n)                 = Just $ (o i) n 2^(bts - i)
        modifyBit i Nothing                  = Just $ (o i) 0 2^(bts - i)
        o i                                  = if i == 1 then (-) else (+)
        bts = bits s

eval ::  Ord l => N.NatFormula l -> A.Assign l -> Int
eval f ass = boolsToInt $ map (flip A.eval ass) f

boolsToInt :: [Bool] -> Int
boolsToInt xs = if null xs then 0 else
                  List.foldl' f initval $ tail xs
                  where f n True = 2 * n + 1
                        f n False = 2 * n
                        initval = if head xs then -1 else 0
