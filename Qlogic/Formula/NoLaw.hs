{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Qlogic.Formula.NoLaw
  (-- * Types
   Formula(..)
  -- * operations
  , literal
  , size
  , simplify
  , atoms
  -- ** utility functions
  , pprintFormula
  )
where 
import qualified Qlogic.Formula as F
import Text.PrettyPrint.HughesPJ
import Qlogic.Boolean

newtype Formula l a = Form (F.Formula l a)

lift f (Form a) = Form a
lift2 f (Form a) (Form b) = Form (f a b)
lift3 f (Form a) (Form b) (Form c) = Form (f a b c)

literal = Form . F.literal

size (Form l) = F.size l

simplify :: (Eq l, Eq a) => Formula l a -> Formula l a
simplify (Form l) = Form (F.simplify l)

atoms (Form l) = F.atoms l

pprintFormula (Form l) = text "Form" <+> F.pprintFormula l

instance (Eq a, Eq l) => Boolean (Formula l a) where
    (Form a) && (Form b) = Form $ F.And [a,b] 
    (Form a) || (Form b) = Form $ F.Or [a,b] 
    not = lift F.Neg
    top = Form F.Top
    bot = Form F.Bot
    (<->) = lift2 F.Iff
    (-->)   = lift2 F.Imp
    ite = lift3 F.Ite


instance (Eq a, Eq l) => NGBoolean (Formula l a) a where
    atom = Form . F.A
