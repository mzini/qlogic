{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Qlogic.SatSolver where

import Control.Monad
import Control.Monad.Trans (lift, liftIO, MonadIO)
import qualified Control.Monad.State.Lazy as State
import qualified Data.HashTable as Hash
import Data.Typeable
import Prelude hiding (negate)
import Qlogic.Utils

import Qlogic.Formula
import qualified Sat as Sat

newtype Clause l = Clause {clauseToList :: [l]}

class SatMonad s where
    solve         :: s Bool
    run           :: s a -> IO a

class SatMonad s => Solver s l where
    newLit        :: s l
    negate        :: l -> s l
    addClause     :: Clause l -> s Bool
    getModelValue :: l -> s Bool

instance MonadIO Sat.S where
  liftIO = Sat.lift

instance SatMonad Sat.S where
    solve         = Sat.solve []
    run           = Sat.run

instance Solver Sat.S Sat.Lit where
    newLit        = Sat.newLit
    negate        = return . Sat.neg
    addClause     = Sat.addClause . clauseToList
    getModelValue = Sat.getModelValue

class Solver s l => IncrementalSolver s l where
    okay :: s () -> s Bool

data Form = Form PropositionalFormula deriving (Eq, Ord, Show, Typeable)
instance ShowLimit Form where
  showlimit n _ | n <= 0 = ""
  showlimit n (Form a)   = "Form " ++ showlimit (n - 1) a
instance PropositionalAtomClass Form

data ExtLit l = Lit l | TopLit | BotLit deriving Eq

data Polarity = PosPol | NegPol

data StateElt l = StateElt { inPos :: Bool, inNeg :: Bool, lit :: ExtLit l }
type SolverState l = Hash.HashTable PropositionalAtom (StateElt l)
type SatSolver s l r = State.StateT (SolverState l) s r

type MiniSat r = SatSolver Sat.S Sat.Lit r

lvar :: PropositionalFormula -> PropositionalAtom
lvar (A x) = x
lvar fm    = PropositionalAtom $ Form fm

shiftPolarity :: Polarity -> Polarity
shiftPolarity PosPol = NegPol
shiftpolarity NegPol = PosPol

inPol :: Polarity -> StateElt l -> Bool
inPol PosPol = inPos
inPol NegPol = inNeg

alit :: (MonadIO s, Solver s l) => PropositionalAtom -> SatSolver s l (ExtLit l)
alit a = do s <- State.get
            lu <- liftIO ({-# SCC "hashLookup" #-} Hash.lookup s a)
            case lu of
              Nothing  -> do theLit <- lift newLit
                             liftIO $ {-# SCC "hashInsert" #-} Hash.insert s a (StateElt {inPos = False, inNeg = False, lit = Lit theLit})
                             return $ Lit theLit
              Just elt -> return $ lit elt
--                 case Hash.lookup a s of
--                   Nothing  -> do theLit <- lift newLit
--                                  State.modify $ addAtom pol a (Lit theLit)
--                                  return $ Lit theLit
--                   Just elt -> if inPol pol elt
--                               then return $ lit elt
--                               else do State.modify $ Hash.adjust (setPol pol) a
--                                       return $ lit elt
--              where addAtom PosPol a l = Hash.insert a (StateElt {inPos = True, inNeg = False, lit = l})
--                    addAtom NegPol a l = Hash.insert a (StateElt {inPos = False, inNeg = True, lit = l})
--                    setPol PosPol elt = elt{inPos=True}
--                    setPol NegPol elt = elt{inNeg=True}

plit :: (MonadIO s, Solver s l) => PropositionalFormula -> SatSolver s l (ExtLit l)
plit (A x)   = alit x
plit Top     = return TopLit
plit Bot     = return BotLit
plit (Neg x) = nlit x
plit fm      = alit $ lvar fm

nlit :: (MonadIO s, Solver s l) => PropositionalFormula -> SatSolver s l (ExtLit l)
nlit fm = plit fm >>= negateLit

negateLit :: (MonadIO s, Solver s l) => ExtLit l -> SatSolver s l (ExtLit l)
negateLit (Lit x) = liftM Lit $ lift $ negate x
negateLit TopLit  = return BotLit
negateLit BotLit  = return TopLit

addLitClause :: (Eq l, MonadIO s, Solver s l) => Clause (ExtLit l) -> SatSolver s l Bool
addLitClause (Clause ls) | elem TopLit ls = return True
                         | otherwise      = {-# SCC "addLitClause" #-} lift $ addClause $ Clause $ foldr f [] ls
                         where f (Lit x) xs = x:xs
                               f BotLit xs  = xs
                               f TopLit xs  = error "TopLit in SatSolver.addLitClause"

maybeCompute_  :: (MonadIO s, Solver s l)
               => Polarity
               -> PropositionalFormula
               -> (ExtLit l -> SatSolver s l (ExtLit l))
               -> SatSolver s l (ExtLit l)
maybeCompute_ pol fm m = {-# SCC "maybeCompute" #-}
  do s <- State.get
     let a = lvar fm
--      if (A a) == fm
--        then
--          do lu <- liftIO (Hash.lookup s a)
--             case lu of
--               Nothing  -> do theLit <- lift newLit
--                              liftIO $ addAtom pol s a (Lit theLit)
--                              m
--               Just elt -> return $ lit elt
--        else do theLit <- lift newLit
--                liftIO $ addAtom pol s a (Lit theLit)
--                return $ Lit theLit
     lu <- liftIO ({-# SCC "hashLookup" #-} Hash.lookup s a)
     case lu of
-- TODO: AS: merge lookup+adjust
       Nothing  -> do theLit <- lift newLit
                      liftIO $ {-# SCC "hashInsert" #-} addAtom pol s a (Lit theLit)
--                       news <- State.get
--                       State.modify $ const news
                      m $ Lit theLit
       Just elt -> if inPol pol elt
                   then return $ lit elt
                   else do liftIO $ {-# SCC "hashInsert" #-} Hash.insert s a (setPol pol elt)
--                            news <- State.get
--                            State.modify $ const news
                           m $ lit elt
   where addAtom PosPol s a l = Hash.insert s a (StateElt {inPos = True, inNeg = False, lit = l})
         addAtom NegPol s a l = Hash.insert s a (StateElt {inPos = False, inNeg = True, lit = l})
         setPol PosPol elt = elt{inPos=True}
         setPol NegPol elt = elt{inNeg=True}

maybeComputePos, maybeComputeNeg :: (MonadIO s, Solver s l)
                                 => PropositionalFormula
                                 -> (ExtLit l -> SatSolver s l (ExtLit l))
                                 -> SatSolver s l (ExtLit l)
maybeComputePos = maybeCompute_ PosPol
maybeComputeNeg = maybeCompute_ NegPol

addPositively :: (Eq l, MonadIO s, Solver s l) => PropositionalFormula -> SatSolver s l (ExtLit l)
addPositively fm@(And as) = {-# SCC "addPosAnd" #-}
  maybeComputePos fm $ \pfm ->
  do nfm <- negateLit pfm
     lits <- mapM addPositively as
     mapM_ (\l -> addLitClause (Clause [nfm, l])) lits
     return pfm
addPositively fm@(Or as) = {-# SCC "addPosOr" #-}
  maybeComputePos fm $ \pfm ->
  do nfm <- negateLit pfm
     lits <- mapM addPositively as
     addLitClause (Clause (nfm:lits))
     return pfm
addPositively fm@(a `Iff` b) = {-# SCC "addPosIff" #-}
  maybeComputePos fm $ \pfm ->
  do nfm <- negateLit pfm
     apos <- addPositively a
     addNegatively a
     aneg <- negateLit apos
     bpos <- addPositively b
     addNegatively b
     bneg <- negateLit bpos
     addLitClause $ Clause [nfm, aneg, bpos]
     addLitClause $ Clause [nfm, apos, bneg]
     return pfm
addPositively fm@(Ite g t e) = {-# SCC "addPosIte" #-}
  maybeComputePos fm $ \pfm ->
  do nfm <- negateLit pfm
     gpos <- addPositively g
     addNegatively g
     gneg <- negateLit gpos
     tpos <- addPositively t
     epos <- addPositively e
     addLitClause $ Clause [nfm, gneg, tpos]
     addLitClause $ Clause [nfm, gpos, epos]
     return pfm
addPositively fm@(a `Imp` b) = {-# SCC "addPosImp" #-}
  maybeComputePos fm $ \pfm ->
  do nfm <- negateLit pfm
     aneg <- addNegatively a >>= negateLit
     bpos <- addPositively b
     addLitClause $ Clause [nfm, aneg, bpos]
     return pfm
addPositively fm@(Neg a) = {-# SCC "addPosNeg" #-} addNegatively a >>= negateLit
addPositively fm@(A _) = {-# SCC "addPosAtom" #-} plit fm
addPositively Top = {-# SCC "addPosTop" #-} return TopLit
addPositively Bot = {-# SCC "addPosBot" #-} return BotLit

addNegatively :: (Eq l, MonadIO s, Solver s l) => PropositionalFormula -> SatSolver s l (ExtLit l)
addNegatively fm@(And as) = {-# SCC "addNegAnd" #-}
  maybeComputeNeg fm $ \pfm ->
  do nlits <- mapM (\l -> addNegatively l >>= negateLit) as
     addLitClause (Clause (pfm:nlits))
     return pfm
addNegatively fm@(Or as) = {-# SCC "addNegOr" #-}
  maybeComputeNeg fm $ \pfm ->
  do nlits <- mapM (\l -> addNegatively l >>= negateLit) as
     mapM_ (\l -> addLitClause (Clause [pfm, l])) nlits
     return pfm
addNegatively fm@(a `Iff` b) = {-# SCC "addNegIff" #-}
  maybeComputeNeg fm $ \pfm ->
  do apos <- addPositively a
     addNegatively a
     aneg <- negateLit apos
     bpos <- addPositively b
     addNegatively b
     bneg <- negateLit bpos
     addLitClause $ Clause [pfm, apos, bpos]
     addLitClause $ Clause [pfm, aneg, bneg]
     return pfm
addNegatively fm@(Ite g t e) = {-# SCC "addNegIte" #-}
  maybeComputeNeg fm $ \pfm ->
  do gpos <- addPositively g
     addNegatively g
     gneg <- negateLit gpos
     tneg <- addNegatively t >>= negateLit
     eneg <- addNegatively e >>= negateLit
     addLitClause $ Clause [pfm, gneg, tneg]
     addLitClause $ Clause [pfm, gpos, eneg]
     return pfm
addNegatively fm@(a `Imp` b) = {-# SCC "addNegImp" #-}
  maybeComputeNeg fm $ \pfm ->
  do apos <- addPositively a
     bneg <- addNegatively b >>= negateLit
     addLitClause $ Clause [pfm, apos]
     addLitClause $ Clause [pfm, bneg]
     return pfm
addNegatively fm@(Neg a) = {-# SCC "addNegNeg" #-} addPositively a >>= negateLit
addNegatively fm@(A _) = {-# SCC "addNegAtom" #-} plit fm
addNegatively Top = {-# SCC "addNegTop" #-} return TopLit
addNegatively Bot = {-# SCC "addNegBot" #-} return BotLit

addFormula :: (Eq l, MonadIO s, Solver s l) => PropositionalFormula -> SatSolver s l ()
addFormula fm = {-# SCC "addFormula" #-}
 do pfm <- plit fm
    addPositively fm
    addLitClause $ Clause [pfm]
    return ()

class Typeable a => Decoder e a | e -> a, a -> e where
  extract :: PropositionalAtom -> Maybe a
  extract (PropositionalAtom a) = cast a
  add :: a -> e -> e

data a :&: b = a :&: b
data OneOf a b = Foo a | Bar b deriving Typeable

instance (Decoder e1 a1, Decoder e2 a2) => Decoder (e1 :&: e2) (OneOf a1 a2) where 
  extract a = case extract a of
                Just a' -> Just $ Foo a'
                Nothing -> case extract a of
                          Just a'  -> Just $ Bar a'
                          Nothing -> Nothing
  add (Foo a) (e1 :&: e2) = add a e1 :&: e2
  add (Bar b) (e1 :&: e2) = e1 :&: (add b e2)

constructValue :: (Decoder e a, MonadIO s, Solver s l) => e -> SatSolver s l e
constructValue e = do s <- State.get >>= liftIO . Hash.toList
--                       ht <- State.get >>= liftIO . Hash.longestChain
--                       liftIO $ putStrLn $ "Longest Chain in Hastable: " ++ show (length ht)
                      foldl f (return e) s
  where f m (a, v) = case extract a of
                       Just a' -> case lit v of
                                    Lit v' -> lift (getModelValue v') >>= \ val -> if val then add a' `liftM` m else m
                                    _ -> m
                       Nothing -> m

ifM :: Monad m =>  m Bool -> m a -> m a -> m a
ifM mc mt me = do c <- mc
                  if c then mt else me

run_ :: (Monad s, SatMonad s) => SatSolver s l r -> IO r
run_ m = do s <- Hash.new (==) (Hash.hashString . {-# SCC "showlimit" #-} showlimit 8)
            run $ State.evalStateT m s

value :: (Decoder e a, MonadIO s, Solver s l) => SatSolver s l () -> e -> IO (Maybe e)
value m p = run_ $ m >> ifM (lift solve) (Just `liftM` constructValue p) (return Nothing)
