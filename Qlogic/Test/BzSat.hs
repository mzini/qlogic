{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import System.IO.Unsafe
import Test.QuickCheck
import Test.QuickCheck.Batch
import Prelude hiding ((&&), (||), max, (+), (<), (<=))
import qualified Prelude as Prelude
import qualified Data.List as List
import Qlogic.Arctic
import Qlogic.BzSat
import qualified Qlogic.ArcSat as AS
import qualified Qlogic.Assign as A
import Qlogic.Boolean
import Qlogic.Formula
import qualified Qlogic.NatSat as N
import Qlogic.MiniSat
import Qlogic.PropositionalFormula
import Qlogic.SatSolver hiding (run)

instance Arbitrary (PropFormula MiniSatLiteral) where
  arbitrary = elements [Top, Bot]

prop_mAddCorrect :: AS.ArcFormula MiniSatLiteral -> AS.ArcFormula MiniSatLiteral -> Property
prop_mAddCorrect ps qs = correctEncoding ps && correctEncoding qs ==> max (litsToNat ps') (litsToNat qs') == eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- N.runNatMonad $ mAdd ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (AS.ArcFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

prop_mTimesCorrect :: AS.ArcFormula MiniSatLiteral -> AS.ArcFormula MiniSatLiteral -> Property
prop_mTimesCorrect ps qs = correctEncoding ps && correctEncoding qs ==> litsToNat ps + litsToNat qs == eval f a
                           where (f, a) = unsafePerformIO $ runSolver $
                                            do (f, fs) <- N.runNatMonad $ mTimes ps qs :: SatSolver MiniSatSolver MiniSatLiteral (AS.ArcFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                               -- addFormula $ bigAnd fs
                                               -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                               let ass = A.empty
                                               return (f, ass)

prop_mGrtCorrect :: AS.ArcFormula MiniSatLiteral -> AS.ArcFormula MiniSatLiteral -> Property
prop_mGrtCorrect ps qs = correctEncoding ps && correctEncoding qs ==> (litsToNat qs' < litsToNat ps') == A.eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- N.runNatMonad $ mGrt ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

prop_mGeqCorrect :: AS.ArcFormula MiniSatLiteral -> AS.ArcFormula MiniSatLiteral -> Property
prop_mGeqCorrect ps qs = correctEncoding ps && correctEncoding qs ==> (litsToNat qs' <= litsToNat ps') == A.eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- N.runNatMonad $ mGeq ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

prop_mEquCorrect :: AS.ArcFormula MiniSatLiteral -> AS.ArcFormula MiniSatLiteral -> Property
prop_mEquCorrect ps qs = correctEncoding ps && correctEncoding qs ==> (litsToNat ps' == litsToNat qs') == A.eval f a
                         where (f, a) = unsafePerformIO $ runSolver $
                                          do (f, fs) <- N.runNatMonad $ mEqu ps' qs' :: SatSolver MiniSatSolver MiniSatLiteral (PropFormula MiniSatLiteral, [PropFormula MiniSatLiteral])
                                             -- addFormula $ bigAnd fs
                                             -- liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                             let ass = A.empty
                                             return (f, ass)
                               ps'    = truncTo 31 ps
                               qs'    = truncTo 31 qs

litsToNat :: AS.ArcFormula MiniSatLiteral -> ArcInt
litsToNat (Top, ps)       = if any (/= Bot) ps then error "Qlogic.Test.BzSat.litsToNat: Incorrect Encoding of MinusInf" else MinusInf
litsToNat (Bot, [])       = Fin 0
litsToNat (Bot, Top : ps) = Fin $ litsToNat' ps - (2 ^ length ps)
litsToNat (Bot, Bot : ps) = Fin $ litsToNat' ps
litstONat (_, _)          = error "Qlogic.Test.BzSat.litsToNat: only works on the formulas Top and Bot"

litsToNat' :: [PropFormula l] -> Int
litsToNat' = List.foldl' f 0
             where f n Top = 2 * n Prelude.+ 1
                   f n Bot = 2 * n
                   f n _   = error "Qlogic.Test.BzSat.litsToNat': only works on the formulas Top and Bot"

correctEncoding :: AS.ArcFormula MiniSatLiteral -> Bool
correctEncoding (Bot, _)  = True
correctEncoding (Top, ps) = all (== Bot) ps
correctEncoding _         = False

options = TestOptions
      { no_of_tests         = 200
      , length_of_tests     = 10
      , debug_tests         = False }

-- main = quickCheck prop_mTimesCorrect

main = do
    runTests "simple" options
        [ run prop_mAddCorrect
        , run prop_mTimesCorrect
        , run prop_mGrtCorrect
        , run prop_mGeqCorrect
        , run prop_mEquCorrect
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
