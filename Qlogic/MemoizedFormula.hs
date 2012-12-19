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

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Qlogic.MemoizedFormula 
    ( toFormula 
    , memoized
    , liftSat
    , MemoFormula
    , Memo)
where 

import System.IO.Unsafe (unsafePerformIO)
import Qlogic.SatSolver
import Qlogic.Formula 
import Qlogic.Boolean
import Qlogic.PropositionalFormula
import Qlogic.SatSolver 
import Control.Monad
import qualified Control.Monad.State.Lazy as State
import qualified Control.Monad.State.Class as StateClass
import Control.Monad.Trans
import qualified Data.Map as Map
import Prelude hiding ((&&),(||),not,foldl,foldr)

data MemoState arg l = St {
      conjs :: [(l, PropFormula l)]
    , lits :: Map.Map arg l
    } deriving (Show)

newtype Memo arg s l r = Memo {
      runMemo:: State.StateT (MemoState arg l) (SatSolver s l) r
    } deriving (Monad, StateClass.MonadState (MemoState arg l))

type MemoFormula arg s l = Memo arg s l (PropFormula l)

initialState :: MemoState arg l
initialState = St [] Map.empty

data L l = Fresh l
         | Old l

cachedLiteral :: (Solver s l, Monad s, Ord arg) => arg -> Memo arg s l (L l)
cachedLiteral arg = do st <- State.get
                       let ls = lits st
                       l <- Memo $ lift freshLit; 
                       case Map.insertLookupWithKey (\ _ _ old -> old) arg l ls of
                         (Just old, _)  -> return $ Old old
                         (Nothing, ls') -> do { State.put st{lits = Map.insert arg l ls}; 
                                               return $ Fresh l;
                                             }

require :: Monad s => l -> PropFormula l -> Memo arg s l ()
require l fm = State.modify $ \ st -> st { conjs = (l,fm) : conjs st}

memoized :: (Solver s l, Ord arg, Eq l) => 
           (arg -> MemoFormula arg s l) -> arg -> MemoFormula arg s l
memoized f arg = do ll <- cachedLiteral arg
                    case ll of 
                      Old l   -> return $ literal l
                      Fresh l -> do { fml <- f arg; 
                                     require l fml;
                                     return $ literal l
                                   }

liftSat :: (Solver s l, Eq l) => SatSolver s l (PropFormula l) -> MemoFormula arg s l
liftSat m = Memo $ lift m

-- toFormula :: (Solver s l, Eq l, State.MonadIO s) => MemoFormula arg s l -> SatSolver s l (PropFormula l)
toFormula (Memo fm) = do (f, st) <- State.runStateT fm initialState
                         mapM (uncurry fix) $ conjs st
                         return $ f
                                      
instance (Monad s, Eq l) => Boolean (MemoFormula arg s l) where
    (&&) = liftM2 (&&)
    (||) = liftM2 (||)
    not = liftM not
    top = return top
    bot = return bot
    (<->) = liftM2 (<->)
    (-->) = liftM2 (-->)
    ite = liftM3 ite
                                                         
instance (Monad s, Eq l, PropAtom a) => NGBoolean (MemoFormula arg s l) a where
    atom = return . atom
    