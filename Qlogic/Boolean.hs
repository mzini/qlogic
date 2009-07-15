{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Qlogic.Boolean where

import Prelude hiding ((&&),(||),not,foldl,foldr)
import qualified Prelude as Prelude
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

  forall :: (Foldable t) => t e -> (e -> a) -> a
  forall xs f = foldr (\ x fm -> f x && fm) top xs 
           
  exist :: (Foldable t) => t e -> (e -> a) -> a
  exist xs f = foldr (\ x fm -> f x || fm) bot xs 

  bigAnd :: Foldable t => t a -> a
  bigAnd = foldr (&&) top

  bigOr :: Foldable t => t a -> a
  bigOr = foldr (||) bot

class Boolean f => NGBoolean f a | f -> a where
    atom :: a -> f

instance Boolean Bool where
  (&&) = (Prelude.&&)
  (||) = (Prelude.||)
  not = Prelude.not
  top = True
  bot = False

liftF :: (b -> b -> b) -> (a -> b) -> (a -> b) -> (a -> b)
liftF o f1 f2 = \a -> f1 a `o` f2 a

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
atmostOne [x] = top
atmostOne (x:xs) = ite x (exactlyNone xs) (atmostOne xs)


oneOrThree :: Boolean a => a -> a -> a -> a
-- ^ demands that exacly one or all three formulas hold
oneOrThree p q r = p <-> q <-> r

twoOrThree :: Boolean a => a -> a -> a -> a
-- ^ demands that exacly two or all three formulas hold.
twoOrThree p q r = (p || q) && (p || r) && (q || r)

