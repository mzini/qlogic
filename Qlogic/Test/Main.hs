module Main where

import Test.QuickCheck
import Test.QuickCheck.Batch 
import Qlogic.MiniSat hiding (run)
import Qlogic.Cnf hiding (top,bot)
import System.IO.Unsafe (unsafePerformIO)
import Qlogic.Formula
import Qlogic.Assign
import Control.Monad (liftM, liftM2)

instance AtomClass Int

-- arbitrary formulas
instance Arbitrary Formula where
  arbitrary = sized arbFm
  coarbitrary = undefined          

arbFm 0 = frequency 
          [ 
           (1,liftM atom (arbitrary::Gen Int))
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
  where bin f = liftM2 f (arbFm m') (arbFm m')
        m' = m `div` 2

-- sat properties
prop_cnf_equisat :: Formula -> Bool
prop_cnf_equisat f = unsafePerformIO $ do f1 <- solve f
                                          f2 <- solveCnf $ fromFormula f
                                          return $  f1 `satEq` f2
  where satEq Nothing Nothing     = True
        satEq (Just _) (Just _) = True
        satEq _ _                             = False

prop_simplify_equisat :: Formula -> Bool
prop_simplify_equisat f = (unsafePerformIO $ solve f) `satEq` (unsafePerformIO $ solve $ simplify f)
  where satEq Nothing Nothing     = True
        satEq (Just _) (Just _) = True
        satEq _ _                             = False

prop_solve_eval :: Formula -> Property
prop_solve_eval fm = isSat res ==> eval fm (ass res)
  where res = unsafePerformIO $ solve fm
        isSat (Just _ ) = True
        isSat _                = False
        ass (Just ass)  = ass

----------------------------------------------------------------------
-- main 

options = TestOptions 
          { no_of_tests     = 1000
          , length_of_tests = 120 -- time limit in seconds
          , debug_tests     = True}

instance AtomClass Char
a = atom 'a'
b = atom 'b'
c = atom 'c'
d = atom 'd'
f = ((bot ||| bot) <->  neg top) &&& (b <-> top ||| neg top)

main = runTests "SatSolving" options
       [
        run prop_cnf_equisat
       , run prop_simplify_equisat
       , run prop_solve_eval
       ]
