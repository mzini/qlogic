module Qlogic.MiniSat 
 (run
  , Answer(..)
  , solve
  , solveCnf
 )

where 
import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import Prelude hiding (mapM_)
import Control.Monad (liftM,mapM)
import Data.Foldable (mapM_)
import Control.Monad.Trans (lift)
import qualified Sat as Sat

import Qlogic.Formula
import Qlogic.Cnf (Literal(..))
import qualified Qlogic.Cnf as Cnf
import qualified Qlogic.Assign as Assign
import Qlogic.Assign ((|->))
import qualified Qlogic.Tseitin as Tseitin

data Answer a = Satisfiable (Assign.Assign a)
            | Unsatisfiable

instance Show a => Show (Answer a) where 
    show (Satisfiable a) = "Satisfiable:" ++ show a
    show Unsatisfiable   = "Unsatisfiable"

type AtmMap a = Map.Map a Sat.Lit

type MiniSat r a = State.StateT (AtmMap a) Sat.S r

newLit :: MiniSat Sat.Lit r 
newLit = lift Sat.newLit

literal :: (Ord a) => a -> MiniSat Sat.Lit a
literal a = do literals <- State.get 
               maybe (newLit >>= \ lit -> State.withStateT (Map.insert a lit) $ return lit)
                     return $ Map.lookup a literals

extractAssign :: Ord a => MiniSat (Assign.Assign a) a
extractAssign = do literals <- State.get
                   Map.foldWithKey f (return Assign.empty) literals
    where f k l m = do assign <- m
                       v <- lift $ Sat.getModelValue l
                       return $ Assign.add [k |-> v] assign

run :: MiniSat r a -> IO r
run m = Sat.run $ State.evalStateT m Map.empty

solve :: (Ord a)  => Formula a -> IO (Answer a)
solve fm = run $ do ans <- solve_ $ Tseitin.transform fm
                    return $ base ans
                      where base Unsatisfiable   = Unsatisfiable
                            base (Satisfiable x) = Satisfiable (Tseitin.baseAssignment x)

solveCnf :: (Ord a) => Cnf.CNF a -> IO (Answer a)
solveCnf = run . solve_

solve_ :: (Ord a) => Cnf.CNF a -> MiniSat (Answer a) a
solve_ fm = do addClauses fm
               isSat <- lift $ Sat.solve []
               case isSat of 
                 True -> Satisfiable `liftM` extractAssign
                 False -> return Unsatisfiable

addClauses :: (Ord a) => Cnf.CNF a -> MiniSat () a
addClauses cnf | Cnf.isContradiction cnf = lift Sat.contradiction
               | otherwise               = Cnf.foldr f (return ()) cnf
  where f clause m = do mlits <- mapM mkLit $ Cnf.clauseToList clause
                        lift $ Sat.addClause mlits
                        m
        mkLit (PosLit l) = literal l
        mkLit (NegLit l) = do l <- literal l
                              return $ Sat.neg l
