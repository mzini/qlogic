{-# LANGUAGE MultiParamTypeClasses #-}

module Qlogic.SatSolver where

import qualified Control.Monad.State.Lazy as State

import qualified Sat as Sat

newtype Clause l = Clause {clauseToList :: [l]}

class Solver s l where
    newLit        :: s l
    negate        :: l -> s l
    addClause     :: Clause l -> s Bool
    getModelValue :: l -> s Bool
    solve         :: s Bool
    run           :: s a -> IO a

instance Solver Sat.S Sat.Lit where 
    newLit        = Sat.newLit
    negate        = return . Sat.neg
    addClause     = Sat.addClause . clauseToList
    getModelValue = Sat.getModelValue
    solve         = Sat.solve []
    run           = Sat.run

class Solver s l => IncrementalSolver s l where
    okay :: s () -> s Bool


-- type SatSolver s r = State.StateT AtomMap s r


-- value :: (Decoder e a) => SatSolver s () -> e -> IO (Maybe e)
-- value = -- run $ 