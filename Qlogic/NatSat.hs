{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}

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
import Control.Monad.Trans (lift)
import qualified Control.Monad.State.Lazy as State
import qualified Control.Monad.State.Class as StateClass
import Qlogic.Formula
import Qlogic.SatSolver
import Prelude hiding ((&&), (||), not)
import Qlogic.Boolean
import Qlogic.PropositionalFormula
import qualified Qlogic.Semiring as SR
import qualified Qlogic.Assign as A
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable
import Qlogic.Utils

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
            | otherwise = (succ . natToBits . (`div` 2)) n

bitsToNat :: Int -> Int
bitsToNat n = (2 ^ n) - 1

bits (Bits n)  = n
bits (Bound n) = natToBits n

bound (Bits n) = bitsToNat n
bound (Bound n) = n

increment :: Size -> Size
increment (Bits n)  = Bits $ n + 1
increment (Bound n) = Bound $ 2 * n + 1

type NatFormula l = [PropFormula l]
data PLVec a = PLVec a Int
  deriving (Eq, Ord, Show, Typeable)

-- instance ShowLimit a => ShowLimit (PLVec a) where
--   showlimit n _ | n <= 0  = ""
--   showlimit n (PLVec a i) = "PLVec " ++ showlimit (n - 1) a ++ show i

instance (Eq a, Ord a, Show a, Typeable a) => PropAtom (PLVec a)

type NatAssign a = Map.Map a Int


newtype NatMonad s l r = NatMonad {runNat :: State.StateT [PropFormula l] (SatSolver s l) r}
    deriving (Monad, StateClass.MonadState [PropFormula l])

liftN :: Solver s l => SatSolver s l r -> NatMonad s l r
liftN = NatMonad . lift

runNatMonad :: NatMonad s l r -> SatSolver s l (r, [PropFormula l])
runNatMonad (NatMonad m) = State.runStateT m []

emptyAssignment :: NatAssign a
emptyAssignment = Map.empty

natToFormula :: Int -> NatFormula l
-- ^ transforms a natural number into a list of Top/Bot values
natToFormula n | n == 0    = [Bot]
               | n == 1    = [Top]
               | n < 0     = error "Only natural numbers allowed in argument!"
               | otherwise = natToFormula (n `div` 2) ++ natToFormula (n `mod` 2)

padBots :: Int -> NatFormula l -> NatFormula l
padBots n | n == 0    = id
          | n > 0     = (Bot :) . padBots (n - 1)
          | otherwise = error "Only natural numbers allowed in argument!"

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


freshVar :: Solver s l => NatMonad s l (PropFormula l)
freshVar = literal `liftM` liftN freshLit

enforce :: Solver s l => [PropFormula l] -> NatMonad s l ()
enforce f = State.modify (f ++)

(.+.) :: Eq l => NatFormula l -> NatFormula l -> NatFormula l
-- ^ performs addition of natural numbers in the representation as a list
--   of propositional formulas
[] .+. []                  = []
[p] .+. [q]                = [p && q, not (p <-> q)]
ps .+. qs | lengthdiff > 0 = padBots lengthdiff ps .+. qs
          | lengthdiff < 0 = ps .+. padBots (-1 * lengthdiff) qs
          | otherwise      = twoOrThree p q r : oneOrThree p q r : tail rs
  where lengthdiff = length qs - length ps
        rs         = tail ps .+. tail qs
        p          = head ps
        q          = head qs
        r          = head rs

mAdd :: (Ord l, Solver s l) => NatFormula l -> NatFormula l -> NatMonad s l (NatFormula l)
-- MA:TODO: l ist nicht typeable, was tun?
mAdd [] []                  = return []
mAdd [p] [q]                = do c <- freshVar
                                 enforce [(p && q) <-> c]
                                 return [c, not (p <-> q)]
mAdd ps qs | lengthdiff > 0 = mAdd (padBots lengthdiff ps) qs
           | lengthdiff < 0 = mAdd ps $ padBots (-1 * lengthdiff) qs
           | otherwise      = do rs <- mAdd (tail ps) (tail qs)
                                 -- let rs = map (patom . PLVec (ps, qs)) [1..length rs']
                                 let r = head rs
                                 c1 <- freshVar
                                 c2 <- freshVar
                                 enforce [twoOrThree p q r <-> c1, oneOrThree p q r <-> c2]
                                 return $ c1 : c2 : tail rs
  where lengthdiff = length qs - length ps
        p          = head ps
        q          = head qs

bigPlus :: Eq l => [NatFormula l] -> NatFormula l
-- ^ calculates the sum of a list of natural numbers in their representation
--   as lists of propositional formulas
bigPlus = foldr (.+.) [Bot]

(.*.) :: Eq l => NatFormula l -> NatFormula l -> NatFormula l
-- ^ performs multiplication of natural numbers in the representation as a list
--   of propositional formulas
_  .*. []     = []
ps .*. [q]    = map (&& q) ps
ps .*. (q:qs) = r1 .+. r2
  where r1 = map (&& q) ps ++ padBots (length qs) []
        r2 = ps .*. qs

mTimes :: (Ord l, Solver s l) => NatFormula l -> NatFormula l -> NatMonad s l (NatFormula l)
mTimes _ []      = return []
mTimes [] _      = return []
mTimes ps [q]    = do return $ map (&& q) ps
mTimes [p] qs    = do return $ map (p &&) qs
mTimes ps (q:qs) = do let r1 = map (&& q) ps ++ padBots (length qs) []
                      r2 <- mTimes ps qs
                      addres <- mAdd r1 r2
                      vs <- mapM (const $ freshVar) [1..length addres]
                      enforce $ zipWith (<->) vs addres
                      return vs

bigTimes :: Eq l => [NatFormula l] -> NatFormula l
-- ^ calculates the product of a list of natural numbers in their representation
--   as lists of propositional formulas
bigTimes = foldr (.*.) [Top]

(.>.) :: Eq l => NatFormula l -> NatFormula l -> PropFormula l
-- ^ performs "greater than" comparisons of natural numbers in the representation
--   as a list of propositional formulas
[] .>. []                  = Bot
[p] .>. [q]                = p && not q
ps .>. qs | lengthdiff > 0 = padBots lengthdiff ps .>. qs
          | lengthdiff < 0 = ps .>. padBots (-1 * lengthdiff) qs
          | otherwise      = (p && not q) || ((p <-> q) && (tail ps .>. tail qs))
   where lengthdiff        = length qs - length ps
         p                 = head ps
         q                 = head qs

(.>=.) :: Eq l => NatFormula l -> NatFormula l -> PropFormula l
-- ^ performs "greater or equal" comparisons of natural numbers in the representation
--   as a list of propositional formulas
[] .>=. []                  = Top
[p] .>=. [q]                = p || not q
ps .>=. qs | lengthdiff > 0 = padBots lengthdiff ps .>=. qs
           | lengthdiff < 0 = ps .>=. padBots (-1 * lengthdiff) qs
           | otherwise      = (p && not q) || ((p <-> q) && (tail ps .>=. tail qs))
    where lengthdiff        = length qs - length ps
          p                 = head ps
          q                 = head qs

(.=.) :: Eq l => NatFormula l -> NatFormula l -> PropFormula l
-- ^ performs equality comparisons of natural numbers in the representation
--   as a list of propositional formulas
[] .=. []                  = Top
[p] .=. [q]                = p <-> q
ps .=. qs | lengthdiff > 0 = padBots lengthdiff ps .=. qs
          | lengthdiff < 0 = ps .=. padBots (-1 * lengthdiff) qs
          | otherwise      = (head ps <-> head qs) && (tail ps .=. tail qs)
   where lengthdiff        = length qs - length ps

-- creates a variable with enough bits to represent n
natAtom :: (PropAtom a, Eq l) => Size -> a -> NatFormula l
-- ^ creates a "natural number variable" encoded by a list of
--   propositional variables. The length of the list is chosen
--   to be exactly enough in order to represent n
natAtom size a = nBitVar (bits size) a

nBitVar :: (PropAtom a, Eq l) => Int -> a -> NatFormula l
nBitVar n v = nBitVar' 1 n v

-- unsafePerformIO $ do putStrLn $ "nBitVar (" ++ show i ++ ") (" ++ show n ++ ") (" ++ show v ++ ")"
--                                                   return $ 

nBitVar' :: (PropAtom a, Eq l) => Int -> Int -> a -> NatFormula l
nBitVar' i n v | i <= n    = propAtom (PLVec v n) : nBitVar' (i + 1) n v
               | otherwise = []

baseFromVec :: (Ord a, Show a, Typeable a) => PLVec a -> a
baseFromVec (PLVec x _) = x

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
eval f ass = boolsToInt $ map (flip A.eval ass) f

boolsToInt :: [Bool] -> Int
boolsToInt = List.foldl' f 0
             where f n True = 2 * n + 1
                   f n False = 2 * n
