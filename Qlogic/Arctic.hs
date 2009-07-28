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
Fin x <= Fin y    = x Prelude.< y
