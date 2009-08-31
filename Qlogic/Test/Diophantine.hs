{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import System.IO.Unsafe
import Test.QuickCheck
import Test.QuickCheck.Batch
import Control.Monad
import Prelude hiding ((<), (<=), max, (+))
import Qlogic.Arctic
import Qlogic.ArcSat
import qualified Qlogic.Assign as A
import Qlogic.Diophantine
import Qlogic.Formula
import Qlogic.MiniSat
import Qlogic.SatSolver hiding (add, run)

instance (Ord l, Solver s l) => MSemiring s l (ArcFormula l) DioVar ArcInt where
  plus = mAdd
  prod = mTimes
  zero = arcToFormula MinusInf
  one  = arcToFormula $ Fin 0
  geq  = (.>=.)
  grt  = (.>.)
  equ  = (.=.)
  constToFormula = arcToFormula
  formAtom = arcAtomM
  truncFormTo = const id

instance Arbitrary ArcInt where
  arbitrary = oneof [elements [MinusInf], liftM Fin arbitrary]

data OpChoose = DoGrt | DoGeq | DoEqu deriving Show

chooseOp :: OpChoose -> DioPoly DioVar ArcInt -> DioPoly DioVar ArcInt -> DioAtom DioVar ArcInt
chooseOp DoGrt = Grt
chooseOp DoGeq = Geq
chooseOp DoEqu = Equ

arcRevOp :: OpChoose -> ArcInt -> ArcInt -> Bool
arcRevOp DoGrt = (<)
arcRevOp DoGeq = (<=)
arcRevOp DoEqu = (==)

instance Arbitrary OpChoose where
  arbitrary = elements [DoGeq, DoGrt, DoEqu]

prop_arcAtomCorrect :: OpChoose -> ArcInt -> ArcInt -> Bool
prop_arcAtomCorrect op m n = (n `op''` m) == A.eval f a
                             where (f, a) = unsafePerformIO $ runSolver $
                                              do fm <- toFormula (Fin 0) $ A $ constToPoly m `op'` constToPoly n
                                                 addFormula fm
                                                 liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                                 ass <- getAssign
                                                 return (fm, ass)
                                   op' = chooseOp op
                                   op'' = arcRevOp op

prop_mAddCorrect :: OpChoose -> ArcInt -> ArcInt -> ArcInt -> ArcInt -> Bool
prop_mAddCorrect op m m' n n' = (max n n' `op''` max m m') == A.eval f a
                                where (f, a) = unsafePerformIO $ runSolver $
                                                 do fm <- toFormula (Fin 0) $ A $ add (constToPoly m) (constToPoly m') `op'` add (constToPoly n) (constToPoly n')
                                                    addFormula fm
                                                    liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                                    ass <- getAssign
                                                    return (fm, ass)
                                      op' = chooseOp op
                                      op'' = arcRevOp op

prop_mTimesCorrect :: OpChoose -> ArcInt -> ArcInt -> ArcInt -> ArcInt -> Bool
prop_mTimesCorrect op m m' n n' = ((n + n') `op''` (m + m')) == A.eval f a
                                  where (f, a) = unsafePerformIO $ runSolver $
                                                   do fm <- toFormula (Fin 0) $ A $ mult (constToPoly m) (constToPoly m') `op'` mult (constToPoly n) (constToPoly n')
                                                      addFormula fm
                                                      liftS solve :: SatSolver MiniSatSolver MiniSatLiteral Bool
                                                      ass <- getAssign
                                                      return (fm, ass)
                                        op' = chooseOp op
                                        op'' = arcRevOp op

options = TestOptions
      { no_of_tests         = 500
      , length_of_tests     = 10
      , debug_tests         = False }

-- main = quickCheck prop_mAddCorrect

main = do
    runTests "simple" options
        [ run prop_arcAtomCorrect
        , run prop_mAddCorrect
        , run prop_mTimesCorrect
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
