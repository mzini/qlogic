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
-- .<<=. is a binary relation such that (x .<=. y && x .<<=. y) <-> x .<. y
  (.<<=.) :: a -> a -> b
  x .<<=. y = x .<. y
-- .>>=. is the inverse of .<<=.
  (.>>=.) :: a -> a -> b
  x .>>=. y = x .>. y

-- class (Ord a, Semiring a) => OrdSemiring a

class (AbstrOrd a b, Semiring a) => AbstrOrdSemiring a b where
