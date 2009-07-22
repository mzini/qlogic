{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Qlogic.MemoizedFormula 
    ( toFormula 
    , memoized
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
import qualified Sat as Sat
import qualified Control.Monad.State.Lazy as State
import qualified Control.Monad.State.Class as StateClass
import Control.Monad.Trans
import qualified Data.Map as Map
import Prelude hiding ((&&),(||),not,foldl,foldr)

data MemoState arg l = St {
      conjs :: [PropFormula l]
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

require :: Monad s => PropFormula l -> Memo arg s l ()
require fm = State.modify $ \ st -> st { conjs = fm : conjs st}

memoized :: (Solver s l, Ord arg, Eq l) => 
           (arg -> MemoFormula arg s l) -> arg -> MemoFormula arg s l
memoized f arg = do ll <- cachedLiteral arg
                    case ll of 
                      Old l   -> return $ literal l
                      Fresh l -> do { fml <- f arg; 
                                     require $ literal l <-> fml;
                                     return $ literal l
                                   }



toFormula :: (Solver s l, Eq l, State.MonadIO s) => MemoFormula arg s l -> SatSolver s l (PropFormula l)
toFormula (Memo fm) = do (f, st) <- State.runStateT fm initialState
                         return $ f && (bigAnd $ conjs st)
    -- where debug st f = liftS $ liftIO 
    --                    ((putStrLn $ show $ lits st) 
    --                     >> (putStrLn "") >> (putStrLn $ show $ Map.size (lits st))
    --                     >> (putStrLn "") >> (putStrLn $ show (conjs st))
    --                     >> (putStrLn "") >> (putStrLn $ show $ length (conjs st))
    --                     >> (putStrLn "") >> (putStrLn $ show f)
    --                     >> (putStrLn "----------------------------------------------------------------------"))
                                      
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
    atom = return . propAtom
    