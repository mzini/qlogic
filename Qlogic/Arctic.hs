module Qlogic.Arctic where

import Prelude hiding ((+), max)
import qualified Prelude as Prelude
import Qlogic.Semiring

data ArcInt = MinusInf | Fin Int
  deriving (Eq, Show)

instance Ord ArcInt where
  MinusInf `compare` MinusInf = EQ
  MinusInf `compare` Fin _ = LT
  Fin _ `compare` MinusInf = GT
  Fin x `compare` Fin y = x `compare` y

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