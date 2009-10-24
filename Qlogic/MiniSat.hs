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

import Control.Monad
import Control.Monad.Trans (lift, MonadIO(..))
import qualified Sat as Sat
import Qlogic.SatSolver
type MiniSatSolver = Sat.S

instance MonadIO MiniSatSolver where 
    liftIO = Sat.lift

type MiniSatLiteral = Sat.Lit

instance Solver MiniSatSolver MiniSatLiteral where
    solve         = Sat.solve []
    run           = Sat.run
    newLit        = Sat.newLit
    negate        = return . Sat.neg
    addClause     = Sat.addClause . clauseToList
    getModelValue = Sat.getModelValue

type MiniSat r = SatSolver MiniSatSolver MiniSatLiteral r

