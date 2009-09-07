{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Qlogic.Semiring where

import Qlogic.Formula
import Qlogic.Boolean
import Qlogic.PropositionalFormula
import Prelude hiding ((&&),(||),not)

class RingConst a where
  czero :: a
  cone :: a
  ringvar :: PropAtom b => b -> a
  restrictvar :: PropAtom b => b -> a

class Semiring a where
  plus :: a -> a -> a
  plus x y = bigPlus [x, y]
  prod :: a -> a -> a
  prod x y = bigProd [x, y]
  zero :: a
  one :: a
  bigPlus :: [a] -> a
  bigPlus = foldr plus zero
  bigProd :: [a] -> a
  bigProd = foldr prod one

class Boolean b => AbstrEq a b where
  (.==.) :: a -> a -> b
  x .==. y = not $ x ./=. y
  (./=.) :: a -> a -> b
  x ./=. y = not $ x .==. y

class AbstrEq a b => AbstrOrd a b where
  (.<.) :: a -> a -> b
  x .<. y = (x .<=. y) && not (x .==. y)
  (.>=.) :: a -> a -> b
  x .>=. y = y .<=. x
  (.>.) :: a -> a -> b
  x .>. y = y .<. x
  (.<=.) :: a -> a -> b
  x .<=. y = x .>=. y

-- class (Ord a, Semiring a) => OrdSemiring a

class (AbstrOrd a b, Semiring a) => AbstrOrdSemiring a b
