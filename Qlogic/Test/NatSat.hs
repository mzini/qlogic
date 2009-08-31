{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import System.IO.Unsafe
import Test.QuickCheck
import Test.QuickCheck.Batch
import Prelude hiding ((&&))
import qualified Data.List as List
import qualified Qlogic.Assign as A
import Qlogic.Boolean
import Qlogic.Formula
import Qlogic.MiniSat
import Qlogic.NatSat
import Qlogic.PropositionalFormula
import Qlogic.SatSolver hiding (run)

instance Arbitrary (PropFormula MiniSatLiteral) where
  arbitrary = elements [Top, Bot]

prop_mAddCorrect :: NatFormula MiniSatLiteral -> NatFormula MiniSatLiteral -> Bool
prop_mAddCorrect ps qs = litsToNat ps + litsToNat qs == eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- runNatMonad $ mAdd ps qs :: SatSolver MiniSatSolver MiniSatLiteral (NatFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)

prop_mTimesCorrect :: NatFormula MiniSatLiteral -> NatFormula MiniSatLiteral -> Bool
prop_mTimesCorrect ps qs = litsToNat ps * litsToNat qs == eval f a
                           where (f, a) = unsafePerformIO $ runSolver $
                                            do (f, fs) <- runNatMonad $ mTimes ps qs :: SatSolver MiniSatSolver MiniSatLiteral (NatFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                               -- addFormula $ bigAnd fs
                                               -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                               let ass = A.empty
                                               return (f, ass)

prop_mGrtCorrect :: NatFormula MiniSatLiteral -> NatFormula MiniSatLiteral -> Bool
prop_mGrtCorrect ps qs = (litsToNat ps' > litsToNat qs') == A.eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- runNatMonad $ mGrt ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

prop_mGeqCorrect :: NatFormula MiniSatLiteral -> NatFormula MiniSatLiteral -> Bool
prop_mGeqCorrect ps qs = (litsToNat ps' >= litsToNat qs') == A.eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- runNatMonad $ mGeq ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

prop_mEquCorrect :: NatFormula MiniSatLiteral -> NatFormula MiniSatLiteral -> Bool
prop_mEquCorrect ps qs = (litsToNat ps' == litsToNat qs') == A.eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- runNatMonad $ mEqu ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

prop_mGeqEqu :: NatFormula MiniSatLiteral -> NatFormula MiniSatLiteral -> Bool
prop_mGeqEqu ps qs = A.eval f a == (A.eval f' a' && A.eval f'' a'')
                     where (f, a)     = unsafePerformIO $ runSolver $
                                          do (f, fs) <- runNatMonad $ mEqu ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             let ass = A.empty
                                             return (f, ass)
                           (f', a')   = unsafePerformIO $ runSolver $
                                          do (f, fs) <- runNatMonad $ mGeq ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             let ass = A.empty
                                             return (f, ass)
                           (f'', a'') = unsafePerformIO $ runSolver $
                                          do (f, fs) <- runNatMonad $ mGeq qs' ps' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             let ass = A.empty
                                             return (f, ass)
                           ps'      = truncTo 31 ps
                           qs'      = truncTo 31 qs

litsToNat :: NatFormula l -> Int
litsToNat = List.foldl' f 0
            where f n Top = 2 * n + 1
                  f n Bot = 2 * n
                  f n _   = error "Qlogic.Test.NatSat.litsToNat: only works on the formulas Top and Bot"

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
        , run prop_mGeqEqu
        ]

-- main = do putStrLn $ show $ fst $ unsafePerformIO $ runSolver (runNatMonad $ mAdd [Top] [Top] :: SatSolver MiniSatSolver MiniSatLiteral (NatFormula MiniSatLiteral, [PropFormula MiniSatLiteral]))
--           putStrLn $ show $ fst $ unsafePerformIO $ runSolver $ (runNatMonad $ maybeFreshVar $ return $ head [Top] && head [Top] :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral]))
--           let (f, a) = unsafePerformIO $ runSolver $
--                          do (f, fs) <- runNatMonad $ mAdd [Top] [Top]
--                             addFormula $ bigAnd fs
--                             liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
--                             ass <- getAssign
--                             return (f, ass)
--           putStrLn $ show $ eval f a
--           quickCheck prop_mAddCorrect
