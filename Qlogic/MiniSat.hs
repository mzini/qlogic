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
import Control.Concurrent.Utils (spawn)
import Control.Exception (evaluate, finally, AsyncException(..))
import Control.Monad (liftM)
import System.IO (hClose, hGetContents, hFlush, hPutStrLn, hPutStr, stderr)
import qualified Data.IntSet as Set
import qualified Data.List as List
import Qlogic.SatSolver
import System.Exit (ExitCode(..))
import System.Process (CreateProcess(..), createProcess, proc, readProcessWithExitCode, StdStream(..), terminateProcess, waitForProcess)

type MiniSatSolver = State.StateT St IO

data St = St { lastLit :: MiniSatLiteral
             , clauseCount :: Int
             , addedFormula :: String
             , assign :: Set.IntSet
             , cmd    :: String}

emptySt :: St
emptySt = St { lastLit = 0, clauseCount = 0, addedFormula = "", assign = Set.empty, cmd = "minisat2"}

type MiniSatLiteral = Int


type MiniSat r = SatSolver MiniSatSolver MiniSatLiteral r

instance Solver MiniSatSolver MiniSatLiteral where
    solve                 = do st <- State.get
                               let hd = "p cnf " ++ show (clauseCount st) ++ " " ++ show (lastLit st) ++ "\n"
                               liftIO $ hPutStr stderr hd
                               out <- liftIO $ spawn (cmd st) ["/dev/stdin","/dev/stdout"] $ hd ++ addedFormula st
                               case (lines . snd) `liftM` out of
                                 Just ("SAT" : satassign : _) -> mapM_ add poslits >> return True
                                     where poslits = filter ((<) 0) $ [(read :: String -> Int) l | l <- words satassign]
                                           add l   = State.modify (\ st -> st{assign = Set.insert l $ assign st})
                                 Just _                          -> return False
                                 Nothing                         -> return False
                               where snd (_, x, _) = x
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

setCmd :: String -> MiniSat ()
setCmd command = liftS $ State.modify (\ st -> st {cmd = command})
