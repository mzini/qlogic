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

module Qlogic.Arctic where

import Prelude hiding ((+), max, (<), (<=))
import qualified Prelude as Prelude
import Qlogic.Semiring

data ArcInt = MinusInf | Fin Int
  deriving (Eq, Ord, Show)

instance Semiring ArcInt where
  plus = max
  prod = (+)
  zero = MinusInf
  one  = Fin 0

arcToInt :: ArcInt -> Int
arcToInt MinusInf = 0
arcToInt (Fin n) = n

max :: ArcInt -> ArcInt -> ArcInt
max MinusInf x = x
max x MinusInf = x
max (Fin x) (Fin y) = Fin $ Prelude.max x y

(+) :: ArcInt -> ArcInt -> ArcInt
MinusInf + _ = MinusInf
_ + MinusInf = MinusInf
(Fin x) + (Fin y) = Fin $ x Prelude.+ y

(<) :: ArcInt -> ArcInt -> Bool
MinusInf < _     = True
Fin _ < MinusInf = False
Fin x < Fin y    = x Prelude.< y

(<=) :: ArcInt -> ArcInt -> Bool
MinusInf <= _     = True
Fin _ <= MinusInf = False
Fin x <= Fin y    = x Prelude.<= y
