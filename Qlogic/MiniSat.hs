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
{-# LANGUAGE TypeSynonymInstances #-}

module Qlogic.MiniSat where

import qualified Control.Monad.State.Lazy as State
import Control.Concurrent (forkOS)
import Control.Concurrent.MVar (takeMVar, putMVar, newEmptyMVar)
import qualified Data.IntSet as Set
import qualified Data.List as List
import Qlogic.SatSolver
import System.Process (readProcessWithExitCode)
import Foreign (unsafePerformIO)

type MiniSatSolver = State.StateT St IO

data St = St { lastLit :: MiniSatLiteral
             , clauseCount :: Int
             , addedFormula :: String
             , assign :: Set.IntSet}

emptySt :: St
emptySt = St { lastLit = 0, clauseCount = 0, addedFormula = "", assign = Set.empty}

type MiniSatLiteral = Int

type MiniSat r = SatSolver MiniSatSolver MiniSatLiteral r

instance Solver MiniSatSolver MiniSatLiteral where
    solve                 = do mv <- liftIO newEmptyMVar
                               st <- State.get
                               liftIO $ forkOS $ minithread mv $ addedFormula st
                               satresult <- liftIO $ takeMVar mv
                               case satresult of
                                 Just satassign -> do (mapM_ addposass $ filter ((<) 0) $ map (read :: String -> Int) $ words satassign)
                                                      -- st'' <- State.get
                                                      -- liftIO $ putStrLn $ show $ assign st''
                                                      return True
                                                        where addposass l = do st' <- State.get
                                                                               State.put st'{assign = Set.insert l $ assign st'}
                                 Nothing        -> return False
                                 where minithread mv cnf = do (exitcode1, stdout, stderr) <- readProcessWithExitCode "minisat" ["/dev/stdin", "/dev/stdout"] cnf
                                                              case lines stdout of
                                                                "SAT" : satassign : _ -> putMVar mv $ Just satassign
                                                                _                     -> putMVar mv Nothing
    run m                 = State.evalStateT m emptySt
    newLit                = do st <- State.get
                               State.put st{lastLit = lastLit st + 1}
                               return $ lastLit st + 1
    negate l              = return $ l * (-1)
    addClause (Clause ls) = do st <- State.get
                               State.put st{clauseCount = clauseCount st + 1, addedFormula = concat (List.intersperse " " (map show ls))  ++ (" 0 " ++ addedFormula st)}
                               return True
    getModelValue l       = do st <- State.get
                               return $ Set.member l $ assign st
