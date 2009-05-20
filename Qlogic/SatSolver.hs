{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Qlogic.SatSolver where

import Control.Monad
import Control.Monad.Trans (lift)
import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import Data.Typeable
import Prelude hiding (negate)

import Qlogic.Formula
import qualified Sat as Sat

newtype Clause l = Clause {clauseToList :: [l]}

class Solver s l where
    newLit        :: s l
    negate        :: l -> s l
    addClause     :: Clause l -> s Bool
    getModelValue :: l -> s Bool
    solve         :: s Bool
    run           :: s a -> IO a

instance Solver Sat.S Sat.Lit where
    newLit        = Sat.newLit
    negate        = return . Sat.neg
    addClause     = Sat.addClause . clauseToList
    getModelValue = Sat.getModelValue
    solve         = Sat.solve []
    run           = Sat.run

class Solver s l => IncrementalSolver s l where
    okay :: s () -> s Bool

data Form = Form PropositionalFormula deriving (Eq, Ord, Show, Typeable)
instance PropositionalAtomClass Form

data ExtLit l = Lit l | TopLit | BotLit deriving Eq

data Polarity = PosPol | NegPol

data StateElt l = StateElt { inPos :: Bool, inNeg :: Bool, lit :: ExtLit l }
type SolverState l = Map.Map PropositionalAtom (StateElt l)
type SatSolver s l r = State.StateT (SolverState l) s r

lvar :: PropositionalFormula -> PropositionalAtom
lvar (A x) = x
lvar fm    = PropositionalAtom $ Form fm

shiftPolarity :: Polarity -> Polarity
shiftPolarity PosPol = NegPol
shiftpolarity NegPol = PosPol

inPol :: Polarity -> StateElt l -> Bool
inPol PosPol = inPos
inPol NegPol = inNeg

alit :: (Monad s, Solver s l) => PropositionalAtom -> SatSolver s l (ExtLit l)
alit a = do s <- State.get
            case Map.lookup a s of
              Nothing  -> do theLit <- lift newLit
                             State.modify $ Map.insert a (StateElt {inPos = False, inNeg = False, lit = Lit theLit})
                             return $ Lit theLit
              Just elt -> return $ lit elt
--                 case Map.lookup a s of
--                   Nothing  -> do theLit <- lift newLit
--                                  State.modify $ addAtom pol a (Lit theLit)
--                                  return $ Lit theLit
--                   Just elt -> if inPol pol elt
--                               then return $ lit elt
--                               else do State.modify $ Map.adjust (setPol pol) a
--                                       return $ lit elt
--              where addAtom PosPol a l = Map.insert a (StateElt {inPos = True, inNeg = False, lit = l})
--                    addAtom NegPol a l = Map.insert a (StateElt {inPos = False, inNeg = True, lit = l})
--                    setPol PosPol elt = elt{inPos=True}
--                    setPol NegPol elt = elt{inNeg=True}

plit :: (Monad s, Solver s l) => PropositionalFormula -> SatSolver s l (ExtLit l)
plit (A x)   = alit x
plit Top     = return TopLit
plit Bot     = return BotLit
plit (Neg x) = nlit x
plit fm      = alit $ lvar fm

nlit :: (Monad s, Solver s l) => PropositionalFormula -> SatSolver s l (ExtLit l)
nlit fm = do l <- plit fm
             negateLit l

negateLit :: (Monad s, Solver s l) => ExtLit l -> SatSolver s l (ExtLit l)
negateLit (Lit x) = liftM Lit $ lift $ negate x
negateLit TopLit  = return BotLit
negateLit BotLit  = return TopLit

addLitClause :: (Eq l, Monad s, Solver s l) => Clause (ExtLit l) -> SatSolver s l Bool
addLitClause (Clause ls) | elem TopLit ls = return True
                         | otherwise      = lift $ addClause $ Clause $ foldr f [] ls
                         where f (Lit x) xs = x:xs
                               f BotLit xs  = xs
                               f TopLit xs  = error "TopLit in SatSolver.addLitClause"

maybeCompute_  :: (Monad s, Solver s l)
               => Polarity
               -> PropositionalFormula
               -> SatSolver s l (ExtLit l)
               -> SatSolver s l (ExtLit l)
maybeCompute_ pol fm m =
  do s <- State.get
     let a = lvar fm
     case Map.lookup a s of
       Nothing  -> do theLit <- lift newLit
                      State.modify $ addAtom pol a (Lit theLit)
                      m
       Just elt -> if inPol pol elt
                   then return $ lit elt
                   else do State.modify $ Map.adjust (setPol pol) a
                           m
  where addAtom PosPol a l = Map.insert a (StateElt {inPos = True, inNeg = False, lit = l})
        addAtom NegPol a l = Map.insert a (StateElt {inPos = False, inNeg = True, lit = l})
        setPol PosPol elt = elt{inPos=True}
        setPol NegPol elt = elt{inNeg=True}

maybeComputePos, maybeComputeNeg :: (Monad s, Solver s l) => PropositionalFormula -> SatSolver s l (ExtLit l) -> SatSolver s l (ExtLit l)
maybeComputePos = maybeCompute_ PosPol
maybeComputeNeg = maybeCompute_ NegPol

addPositively :: (Eq l, Monad s, Solver s l) => PropositionalFormula -> SatSolver s l (ExtLit l)
addPositively fm@(And as) =
  maybeComputePos fm $
  do nfm <- nlit fm
     lits <- mapM addPositively as
     mapM_ (\l -> addLitClause (Clause [nfm, l])) lits
     plit fm
addPositively fm@(Or as) =
  maybeComputePos fm $
  do nfm <- nlit fm
     lits <- mapM addPositively as
     addLitClause (Clause (nfm:lits))
     plit fm
addPositively fm@(a `Iff` b) =
  maybeComputePos fm $
  do nfm <- nlit fm
     apos <- addPositively a
     addNegatively a
     aneg <- negateLit apos
     bpos <- addPositively b
     addNegatively b
     bneg <- negateLit bpos
     addLitClause $ Clause [nfm, aneg, bpos]
     addLitClause $ Clause [nfm, apos, bneg]
     plit fm
addPositively fm@(Ite g t e) =
  maybeComputePos fm $
  do nfm <- nlit fm
     gpos <- addPositively g
     addNegatively g
     gneg <- negateLit gpos
     tpos <- addPositively t
     epos <- addPositively e
     addLitClause $ Clause [nfm, gneg, tpos]
     addLitClause $ Clause [nfm, gpos, epos]
     plit fm
addPositively fm@(a `Imp` b) =
  maybeComputePos fm $
  do nfm <- nlit fm
     aneg <- addNegatively a >>= negateLit
     bpos <- addPositively b
     addLitClause $ Clause [nfm, aneg, bpos]
     plit fm
addPositively fm@(Neg a) = maybeComputePos fm $ addNegatively a >>= negateLit
addPositively fm@(A _) = plit fm
addPositively Top = return TopLit
addPositively Bot = return BotLit

addNegatively :: (Eq l, Monad s, Solver s l) => PropositionalFormula -> SatSolver s l (ExtLit l)
addNegatively fm@(And as) =
  maybeComputeNeg fm $
  do pfm <- plit fm
     nlits <- mapM (\l -> addNegatively l >>= negateLit) as
     addLitClause (Clause (pfm:nlits))
     return pfm
addNegatively fm@(Or as) =
  maybeComputeNeg fm $
  do pfm <- plit fm
     nlits <- mapM (\l -> addNegatively l >>= negateLit) as
     mapM_ (\l -> addLitClause (Clause [pfm, l])) nlits
     return pfm
addNegatively fm@(a `Iff` b) =
  maybeComputeNeg fm $
  do pfm <- plit fm
     apos <- addPositively a
     addNegatively a
     aneg <- negateLit apos
     bpos <- addPositively b
     addNegatively b
     bneg <- negateLit bpos
     addLitClause $ Clause [pfm, apos, bpos]
     addLitClause $ Clause [pfm, aneg, bneg]
     return pfm
addNegatively fm@(Ite g t e) =
  maybeComputeNeg fm $
  do pfm <- plit fm
     gpos <- addPositively g
     addNegatively g
     gneg <- negateLit gpos
     tneg <- addNegatively t >>= negateLit
     eneg <- addNegatively e >>= negateLit
     addLitClause $ Clause [pfm, gneg, tneg]
     addLitClause $ Clause [pfm, gpos, eneg]
     return pfm
addNegatively fm@(a `Imp` b) =
  maybeComputeNeg fm $
  do pfm <- plit fm
     apos <- addPositively a
     bneg <- addNegatively b >>= negateLit
     addLitClause $ Clause [pfm, apos]
     addLitClause $ Clause [pfm, bneg]
     return pfm
addNegatively fm@(Neg a) = maybeComputeNeg fm $ addPositively a >>= negateLit
addNegatively fm@(A _) = plit fm
addNegatively Top = return TopLit
addNegatively Bot = return BotLit

addFormula :: (Eq l, Monad s, Solver s l) => PropositionalFormula -> SatSolver s l Bool
addFormula fm = do pfm <- plit fm
                   addPositively fm
                   addLitClause $ Clause [pfm]

-- value :: (Decoder e a) => SatSolver s () -> e -> IO (Maybe e)
-- value = -- run $ 
