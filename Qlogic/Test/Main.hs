module Main where

import Test.QuickCheck
import Test.QuickCheck.Batch 
import Qlogic.MiniSat hiding (run)
import Qlogic.Cnf
import System.IO.Unsafe (unsafePerformIO)
import Qlogic.Formula
import Control.Monad (liftM, liftM2)

-- arbitrary formulas
instance Arbitrary a => Arbitrary (Formula a) where
  arbitrary = sized arbFm
  coarbitrary = undefined          

arbFm 0 = frequency 
          [ 
           (1,liftM Atom arbitrary)
          , (1,return Top)
          , (1,return Bot)
          ]
arbFm m = frequency
          [ 
           (1, bin And)
          , (1, bin Or)
          , (1, bin Iff)
          , (1, bin Imp)
          , (1, liftM Neg (arbFm $ m - 1 ))
          ]
  where bin f = do liftM2 f (arbFm m') (arbFm m')
        m' = m `div` 2

-- sat properties
prop_cnf_equisat :: Formula Int -> Bool
prop_cnf_equisat f = (unsafePerformIO $ solve f) `satEq` (unsafePerformIO $ solveCnf $ fromFormula f)
  where satEq Unsatisfiable Unsatisfiable     = True
        satEq (Satisfiable _) (Satisfiable _) = True
        satEq _ _                             = False

prop_simplify_equisat :: Formula Int -> Bool
prop_simplify_equisat f = (unsafePerformIO $ solve f) `satEq` (unsafePerformIO $ solve $ simplify f)
  where satEq Unsatisfiable Unsatisfiable     = True
        satEq (Satisfiable _) (Satisfiable _) = True
        satEq _ _                             = False

prop_solve_eval :: Formula Int -> Property
prop_solve_eval fm = isSat res ==> eval fm (ass res)
  where res = unsafePerformIO $ solve fm
        isSat (Satisfiable _ ) = True
        isSat _                = False
        ass (Satisfiable ass)  = ass

----------------------------------------------------------------------
-- main 

options = TestOptions 
          { no_of_tests     = 1000
          , length_of_tests = 120 -- time limit in seconds
          , debug_tests     = False}

main = runTests "SatSolving" options
       [
        run prop_cnf_equisat
       , run prop_simplify_equisat
       , run prop_solve_eval
       ]
