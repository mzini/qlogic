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

{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}

module Qlogic.PropositionalFormula where
import Qlogic.Utils
import qualified Qlogic.Formula as Fm
import Qlogic.Boolean
import Data.Typeable

class (Eq a, Ord a, Show a, Typeable a) => PropAtom a
  -- where
  --           toPropositionalAtom :: a -> PropositionalAtom
  --           toPropositionalAtom = PropositionalAtom
  --           fromPropositionalAtom :: PropositionalAtom -> Maybe a
  --           fromPropositionalAtom (PropositionalAtom a) = cast a

data PA = forall a. (PropAtom a) => PA a deriving Typeable

type PropFormula l = Fm.Formula l PA


compare_ :: PA -> PA -> Ordering
PA (a :: at) `compare_` PA (b :: bt) 
    | ta == tb = (cast a :: Maybe at) `compare` (cast b :: Maybe at)
    | otherwise = show ta `compare` show tb 
   where ta = typeOf a
         tb = typeOf b

instance Eq PA where
  a == b = a `compare_` b == EQ

instance Ord PA where
  compare = compare_

instance Show PA where
  show (PA a) = "PA " ++ show  a

propAtom :: (Eq l, PropAtom a) => a -> PropFormula l
propAtom = atom . PA

