module Qlogic.MiniSat where
import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import qualified Qlogic.Assign as Assign
import Qlogic.Assign ((|->))
import Control.Monad (liftM, mapM_)
import Control.Monad.Trans (lift)
import qualified Sat as Sat
import Qlogic.Formula
import qualified Qlogic.Tseitin as Tseitin

data Answer a = Satisfiable (Assign.Assign a)
            | Unsatisfiable

instance Show a => Show (Answer a) where 
    show (Satisfiable a) = "Satisfiable:" ++ show a
    show Unsatisfiable   = "Unsatisfiable"

type AtmMap a = Map.Map (Tseitin.ExtendedAtom a) Sat.Lit

type MiniSat r a = State.StateT (AtmMap a) Sat.S r

newLit :: MiniSat Sat.Lit r 
newLit = lift Sat.newLit

literal :: (Ord a) => (Tseitin.ExtendedAtom a) -> MiniSat Sat.Lit a
literal a = do literals <- State.get 
               maybe (newLit >>= \ lit -> State.withStateT (Map.insert a lit) $ return lit)
                     return $ Map.lookup a literals


addClauses :: (Ord a,Show a) => Formula a -> MiniSat () a
addClauses f = do mapM_ addClause' cnf
                  lift $ Sat.lift $ putStrLn $ show cnf
                  return ()
  where cnf = Tseitin.transform f
        addClause' clause | Tseitin.TopLit `elem` clause = return ()
                          | otherwise                    = do mlits <- (mapM mkLit . filter Tseitin.isVarLit) clause
                                                              lift $ Sat.addClause mlits
                                                              return ()
        mkLit (Tseitin.PosLit l) = literal l
        mkLit (Tseitin.NegLit l) = do l <- literal l
                                      return $ Sat.neg l
        mkLit _                  = error "Somebody set up us the bomb!"


extractAssign :: Ord a => MiniSat (Assign.Assign a) a
extractAssign = do literals <- State.get
                   map <- Map.foldWithKey f (return Assign.empty) literals
                   return $ Tseitin.baseAssignment map
    where f k l m = do assign <- m
                       v <- lift $ Sat.getValue l
                       return $ Assign.bind [k |-> v] assign

run :: MiniSat r a -> IO r
run m = Sat.run $ State.evalStateT m Map.empty

solve :: (Ord a, Show a)  => Formula a -> IO (Answer a)
solve fm = run (solve_ fm)

solve_ :: (Show a, Ord a) => Formula a -> MiniSat (Answer a) a
solve_ fm = do addClauses fm
               isSat <- lift Sat.okay
               case isSat of 
                 True -> Satisfiable `liftM` extractAssign
                 False -> return Unsatisfiable

