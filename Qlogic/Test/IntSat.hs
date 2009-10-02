{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import System.IO.Unsafe
import Test.QuickCheck
import Test.QuickCheck.Batch
import Prelude hiding ((&&))
import qualified Prelude as Prelude
import qualified Data.List as List
import qualified Qlogic.Assign as A
import Qlogic.Boolean
import Qlogic.Formula
import Qlogic.MiniSat
import Qlogic.IntSat
import qualified Qlogic.NatSat as N
import Qlogic.PropositionalFormula
import Qlogic.SatSolver hiding (run)

instance Arbitrary (PropFormula MiniSatLiteral) where
  arbitrary = elements [Top, Bot]

prop_mAddCorrect :: N.NatFormula MiniSatLiteral -> N.NatFormula MiniSatLiteral -> Bool
prop_mAddCorrect ps qs = litsToNat ps' + litsToNat qs' == eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- N.runNatMonad $ mAdd ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (N.NatFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

prop_mTimesCorrect :: N.NatFormula MiniSatLiteral -> N.NatFormula MiniSatLiteral -> Bool
prop_mTimesCorrect ps qs = litsToNat ps * litsToNat qs == eval f a
                           where (f, a) = unsafePerformIO $ runSolver $
                                            do (f, fs) <- N.runNatMonad $ mTimes ps qs :: SatSolver MiniSatSolver MiniSatLiteral (N.NatFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                               -- addFormula $ bigAnd fs
                                               -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                               let ass = A.empty
                                               return (f, ass)

prop_mGrtCorrect :: N.NatFormula MiniSatLiteral -> N.NatFormula MiniSatLiteral -> Bool
prop_mGrtCorrect ps qs = (litsToNat qs' < litsToNat ps') == A.eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- N.runNatMonad $ mGrt ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

prop_mGeqCorrect :: N.NatFormula MiniSatLiteral -> N.NatFormula MiniSatLiteral -> Bool
prop_mGeqCorrect ps qs = (litsToNat qs' <= litsToNat ps') == A.eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- N.runNatMonad $ mGeq ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

prop_mEquCorrect :: N.NatFormula MiniSatLiteral -> N.NatFormula MiniSatLiteral -> Bool
prop_mEquCorrect ps qs = (litsToNat ps' == litsToNat qs') == A.eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- N.runNatMonad $ mEqu ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

litsToNat :: N.NatFormula MiniSatLiteral -> Int
litsToNat []         = 0
litsToNat (Top : ps) = litsToNat' ps - (2 ^ length ps)
litsToNat (Bot : ps) = litsToNat' ps
litstONat _          = error "Qlogic.Test.IntSat.litsToNat: only works on the formulas Top and Bot"

litsToNat' :: [PropFormula l] -> Int
litsToNat' = List.foldl' f 0
             where f n Top = 2 * n Prelude.+ 1
                   f n Bot = 2 * n
                   f n _   = error "Qlogic.Test.IntSat.litsToNat': only works on the formulas Top and Bot"

options = TestOptions
      { no_of_tests         = 200
      , length_of_tests     = 10
      , debug_tests         = False }

-- main = quickCheck prop_mGrtCorrect

main = do
    runTests "simple" options
        [ run prop_mAddCorrect
        , run prop_mTimesCorrect
        , run prop_mGrtCorrect
        , run prop_mGeqCorrect
        , run prop_mEquCorrect
        ]

-- main = do putStrLn $ show $ fst $ unsafePerformIO $ runSolver (runNatMonad $ mAdd [Top] [Top] :: SatSolver MiniSatSolver MiniSatLiteral (N.NatFormula MiniSatLiteral, [PropFormula MiniSatLiteral]))
--           putStrLn $ show $ fst $ unsafePerformIO $ runSolver $ (runNatMonad $ maybeFreshVar $ return $ head [Top] && head [Top] :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral]))
--           let (f, a) = unsafePerformIO $ runSolver $
--                          do (f, fs) <- runNatMonad $ mAdd [Top] [Top]
--                             addFormula $ bigAnd fs
--                             liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
--                             ass <- getAssign
--                             return (f, ass)
--           putStrLn $ show $ eval f a
--           quickCheck prop_mAddCorrect
