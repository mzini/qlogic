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
{-# LANGUAGE DeriveDataTypeable #-}

module Qlogic.Formula
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
import Prelude hiding ((&&),(||),not,foldl,foldr)
import Data.Foldable
import Data.Set (Set)
import Data.Typeable
import Qlogic.Boolean
import Qlogic.Utils
import Text.PrettyPrint.HughesPJ
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import qualified Prelude as Prelude

data Formula l a = A a
                 | SL l
                 | And [Formula l a]
                 | Or  [Formula l a]
                 | Iff (Formula l a) (Formula l a)
                 | Ite (Formula l a) (Formula l a) (Formula l a)
                 | Imp (Formula l a) (Formula l a)
                 | Neg (Formula l a)
                 | Top
                 | Bot deriving (Eq, Ord, Typeable, Show)

instance (Eq a, Eq l) => Boolean (Formula l a) where
    Top      && b        = b
    Bot      && _        = Bot
    a        && Top      = a
    _        && Bot      = Bot
    (And l1) && (And l2) = And $ l1 ++ l2
    (And l1) && b        = And $ l1 ++ [b]
    a        && (And l2) = And $ a:l2
    a        && (Neg b)  | a == b    = Bot
    a        && b        | a == b    = a
    a        && b        | otherwise = And [a,b]

    Top     || _       = Top
    Bot     || b       = b
    _       || Top     = Top
    a       || Bot     = a
    (Or l1) || (Or l2) = Or $ l1 ++ l2
    (Or l1) || b       = Or $ l1 ++ [b]
    a       || (Neg b) | a == b    = Top
    a       || b       | a == b    = a
    a       || b       | otherwise = Or [a,b]

    not Bot     = Top
    not Top     = Bot
    not (Neg a) = a
    not a       = Neg a

    top = Top

    bot = Bot

    Top <-> b   = b
    Bot <-> b   = not b
    a   <-> Top = a
    a   <-> Bot = not a
    a   <-> (Neg b)  | a == b    = Bot
    a   <-> b        | a == b    = Top
    a   <-> b        | otherwise = a `Iff` b

    Top --> b   = b
    Bot --> _   = Top
    _   --> Top = Top
    a   --> Bot = not a
    a   --> (Neg b) | a == b    = Bot
    a   --> b       | a == b    = Top
    a   --> b       | otherwise = a `Imp` b

    ite Top t       _ = t
    ite Bot _       e = e
    ite g   Bot     e = not g && e
    ite g   t   Bot   = g && t
    ite g       t   e = Ite g t e


instance (Eq a, Eq l) => NGBoolean (Formula l a) a where
    atom = A

literal :: l -> Formula l a
literal = SL

atoms :: (Ord a, Ord l) => Formula l a -> Set (Either l a)
atoms (A a)       = Set.singleton (Right a)
atoms (SL a)       = Set.singleton (Left a)
atoms (And l)     = Set.unions [atoms e | e <- l]
atoms (Or l)      = Set.unions [atoms e | e <- l]
atoms (a `Iff` b) = atoms a `Set.union` atoms b
atoms (Ite a b c) = Set.unions [atoms a, atoms b, atoms c]
atoms (a `Imp` b) = atoms a `Set.union`atoms b
atoms (Neg a)     = atoms a
atoms Top         = Set.empty
atoms Bot         = Set.empty

simplify :: (Eq l, Eq a) => Formula l a -> Formula l a
-- ^ performs basic simplification of formulas
simplify (And l)     = bigAnd [simplify e | e <- l]
simplify (Or l)      = bigAnd [simplify e | e <- l]
simplify (a `Iff` b) = simplify a <-> simplify b
simplify (a `Imp` b) = simplify a --> simplify b
simplify (Neg a)     = not $ simplify a
simplify a           = a


size :: Formula l a -> Int
size (A a)       = 1
size (SL a)      = 1
size (And xs)    = 1 + Prelude.sum (map size xs)
size (Or xs)     = 1 + Prelude.sum (map size xs)
size (Iff a b)   = size a + size b + 1
size (Ite a b c) = size a + size b + size c + 1
size (Imp a b)   = size a + size b + 1
size (Neg a)     = size a + 1
size Top         = 1
size Bot         = 1

pprintBinFm :: (Show a, Show l) => String -> Formula l a -> Formula l a -> Doc
pprintBinFm s a b = parens $ text s <+> (pprintFormula a $$ pprintFormula b)

pprintFormula :: (Show a, Show l) => Formula l a -> Doc
pprintFormula (A a)       = text $ show a
pprintFormula (SL a)      = text $ show a
pprintFormula (And l)     = parens $ text "/\\" <+> sep (punctuate (text " ") $ map pprintFormula l)
pprintFormula (Or l)      = parens $ text "\\/" <+> sep (punctuate (text " ") $ map pprintFormula l)
pprintFormula (Iff a b)   = pprintBinFm "<->" a b
pprintFormula (Imp a b)   = pprintBinFm "-->" a b
pprintFormula (Ite a b c) = parens $ text "ite" <+> (pprintFormula a $$ pprintFormula b $$ pprintFormula c)
pprintFormula (Neg a)     = parens $ text "-" <+> (pprintFormula a)
pprintFormula Top         = text "T"
pprintFormula Bot         = text "F"
