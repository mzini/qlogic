{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
module Qlogic.PropositionalFormula where
import Qlogic.Utils
import qualified Qlogic.Formula as Fm
import Qlogic.Boolean
import Data.Typeable

class (Eq a, Ord a, Show a, ShowLimit a, Typeable a) => PropAtom a
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
  show (PA a) = "PropositionalAtom " ++ show  a

instance ShowLimit PA where
  showlimit n _ | n <= 0            = ""
  showlimit n (PA a) = "PA " ++ showlimit (n - 1) a

instance PropAtom PA

propAtom :: (Eq l, PropAtom a) => a -> PropFormula l
propAtom = atom . PA

