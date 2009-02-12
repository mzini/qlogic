module Qlogic.MiniSat where
import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import qualified Qlogic.Assign as Assign

data Answer a = Satisfiable (Assign.Assign a)
            | Unsatisfiable

type AtmMap a = Map.Map a (Maybe Bool)

-- data MiniSat a b = StateT (AtmMap a) (S.S b) a