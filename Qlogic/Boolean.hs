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
{-# LANGUAGE TypeFamilies #-}

module Qlogic.Boolean where

import Control.Monad
import Prelude hiding ((&&),(||),not,foldl,foldr)
import qualified Prelude
import Data.Foldable

infixr 3 &&
infixr 2 ||
infixr 1 -->
infixr 1 <->

class Boolean a where
  (&&) :: a -> a -> a
  (||) :: a -> a -> a
  not :: a -> a
  top :: a
  bot :: a
  
  (<->) :: a -> a -> a
  a <-> b = (a --> b) && (b --> a)

  (-->) :: a -> a -> a 
  a --> b = not a || b

  ite :: a -> a -> a -> a
  ite g t e = (g --> t) && (not g --> e)

  maj :: a -> a -> a -> a
  maj a b c = (a || b) && (a || c) && (b || c)

  odd3 :: a -> a -> a -> a
  odd3 a b c = a <-> b <-> c

  forall :: (Foldable t) => t e -> (e -> a) -> a
  forall xs f = foldr (\ x frm -> f x && frm) top xs 
           
  exist :: (Foldable t) => t e -> (e -> a) -> a
  exist xs f = foldr (\ x frm -> f x || frm) bot xs 

  bigAnd :: Foldable t => t a -> a
  bigAnd = foldr (&&) top

  bigOr :: Foldable t => t a -> a
  bigOr = foldr (||) bot

class Boolean f => NGBoolean f where
    type Atom f
    atom :: Atom f -> f

instance Boolean Bool where
  (&&) = (Prelude.&&)
  (||) = (Prelude.||)
  not = Prelude.not
  top = True
  bot = False

liftF :: (b -> b -> b) -> (a -> b) -> (a -> b) -> a -> b
liftF o f1 f2 a = f1 a `o` f2 a

instance Boolean b => Boolean (a -> b) where
  (&&)  = liftF (&&)
  (||)  = liftF (||)
  not f = not . f
  top   = const top
  bot   = const bot

fm :: Boolean a => Bool -> a
fm True  = top
fm False = bot


exactlyNone :: Boolean a => [a] -> a
exactlyNone xs = forall xs not

exactlyOne :: Boolean a => [a] -> a
exactlyOne []     = bot
exactlyOne (x:xs) = ite x (exactlyNone xs) (exactlyOne xs)

atmostOne :: Boolean a => [a] -> a
atmostOne [] = top
atmostOne [_] = top
atmostOne (x:xs) = ite x (exactlyNone xs) (atmostOne xs)


oneOrThree :: Boolean a => a -> a -> a -> a
-- ^ demands that exacly one or all three formulas hold
oneOrThree = odd3

twoOrThree :: Boolean a => a -> a -> a -> a
-- ^ demands that exacly two or all three formulas hold.
twoOrThree = maj
