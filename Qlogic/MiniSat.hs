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

