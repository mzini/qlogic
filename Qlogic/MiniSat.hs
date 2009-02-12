module Qlogic.MiniSat where
import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import qualified Qlogic.Assign as Assign
import Qlogic.Assign ((|->))
import Control.Monad (liftM, mapM_)
import Control.Monad.Trans (lift)
import qualified Sat as Sat
import Qlogic.Formula

data Answer a = Satisfiable (Assign.Assign a)
            | Unsatisfiable

instance Show a => Show (Answer a) where 
    show (Satisfiable a) = "Satisfiable:" ++ show a
    show Unsatisfiable   = "Unsatisfiable"

type AtmMap a = Map.Map a Sat.Lit

type MiniSat r a = State.StateT (AtmMap a) Sat.S r
type CNF = [[Sat.Lit]]

newLit :: MiniSat Sat.Lit r 
newLit = lift Sat.newLit

literal :: (Ord a) => a -> MiniSat Sat.Lit a
literal a = do literals <- State.get 
               maybe (newLit >>= \ lit -> State.withStateT (Map.insert a lit) $ return lit)
                     return $ Map.lookup a literals

addAsClauses :: Formula a -> MiniSat CNF a
addAsClauses f = do l1 <- newLit
                    l2 <- newLit
                    return [[l1,l2]]

extractAssign :: Ord a => MiniSat (Assign.Assign a) a
extractAssign = do literals <- State.get
                   Map.foldWithKey f (return Assign.empty) literals
    where f k l m = do assign <- m
                       v <- lift $ Sat.getValue l
                       return $ Assign.bind [k |-> v] assign

run :: MiniSat r a -> IO r
run m = Sat.run $ State.evalStateT m Map.empty

solve :: (Ord a)  => Formula a -> IO (Answer a)
solve fm = run (solve_ fm)

solve_ :: (Ord a) => Formula a -> MiniSat (Answer a) a
solve_ fm = do addAsClauses fm
               isSat <- lift Sat.okay
               case isSat of 
                 True -> Satisfiable `liftM` extractAssign
                 False -> return Unsatisfiable

