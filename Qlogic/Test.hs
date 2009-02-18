module Test where

import Test.QuickCheck
import Qlogic.MiniSat
import Qlogic.Cnf

-- AS: Skeleton
prop_cnfEquisat f = (solve f) `satEq` ((solveCnf . fromFormula) f)

satEq Unsatisfiable Unsatisfiable = True
satEq (Satisfiable _) (Satisfiable _) = True
satEq _ _ = False
