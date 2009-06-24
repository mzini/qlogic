{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Qlogic.SatSolver 
    (
     SatSolver(..)
    , Solver(..)
    , Clause(..)
    , Decoder(..)
    , (:&:) (..)
    , addFormula
    , value
    , freshLit
    )
where

import Control.Monad
import Control.Monad.Trans (lift)
import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import Data.Typeable
import qualified Control.Monad.State.Class as StateClass
import Prelude hiding (negate)

import Qlogic.Formula
import Qlogic.PropositionalFormula

newtype Clause l = Clause {clauseToList :: [l]}

class Monad s => Solver s l | s -> l where
    solve         :: s Bool
    run           :: s a -> IO a
    newLit        :: s l
    negate        :: l -> s l
    addClause     :: Clause l -> s Bool
    getModelValue :: l -> s Bool

class Solver s l => IncrementalSolver s l where
    okay :: s () -> s Bool

data ExtLit l = Lit !l | TopLit | BotLit deriving Eq

data Polarity = PosPol | NegPol

newtype SatSolver s l r = SatSolver {runSolver :: State.StateT (Map.Map PA l) s r} 
    deriving (Monad, StateClass.MonadState (Map.Map PA l))

liftS :: Solver s l => s r -> SatSolver s l r 
liftS = SatSolver . lift

freshLit :: Solver s l => SatSolver s l l
freshLit = liftS newLit

freshELit :: Solver s l => SatSolver s l (ExtLit l)
freshELit = Lit `liftM` freshLit

atomToELit :: Solver s l => PA -> SatSolver s l (ExtLit l)
atomToELit a = do litMap <- State.get
                  l <- freshLit
                  case Map.insertLookupWithKey (\ _ _ oldLit -> oldLit) a l litMap of
                    (Just oldLit, _)  -> return $ Lit oldLit
                    (Nothing, newMap) -> State.put newMap >> return (Lit l)

negateELit :: (Solver s l) => ExtLit l -> SatSolver s l (ExtLit l)
negateELit (Lit x) = Lit `liftM` liftS  (negate x)
negateELit TopLit  = return BotLit
negateELit BotLit  = return TopLit

plit :: (Monad s, Solver s l) => PropFormula l -> SatSolver s l (ExtLit l)
plit (A x)   = atomToELit x
plit (SL x)  = return $ Lit x
plit Top     = return TopLit
plit Bot     = return BotLit
plit (Neg x) = nlit x
plit fm      = freshELit

nlit :: (Monad s, Solver s l) => PropFormula l -> SatSolver s l (ExtLit l)
nlit fm = plit fm >>= negateELit

freshELits :: (Monad s, Solver s l) => SatSolver s l (ExtLit l, ExtLit l)
freshELits = do p <- freshELit
                n <- negateELit p
                return (p,n)
     
addLitClause :: (Eq l, Solver s l) => Clause (ExtLit l) -> SatSolver s l Bool
addLitClause (Clause ls) = case foldr f (Just []) ls of 
                             Nothing -> return True
                             Just lits -> liftS $ addClause $ Clause lits
    where f (Lit x) (Just xs) = Just $ x:xs
          f BotLit  xs        = xs
          f TopLit  xs        = Nothing
          f _       Nothing   = Nothing

addPositively :: (Eq l, Solver s l) => PropFormula l -> SatSolver s l (ExtLit l)
addPositively fm@(And as) =
  do (p,n) <- freshELits
     plits <- mapM addPositively as
     mapM_ (\l -> addLitClause $ Clause [n, l]) plits
     return p
addPositively fm@(Or as) = 
  do (p,n) <- freshELits
     plits <- mapM addPositively as
     addLitClause $ Clause $ n:plits
     return p
addPositively fm@(a `Iff` b) = 
  do (p,n) <- freshELits
     apos <- addPositively a
     aneg <- addNegatively a >>= negateELit 
     bpos <- addPositively b
     bneg <- addNegatively b >>= negateELit
     addLitClause $ Clause [n, aneg, bpos]
     addLitClause $ Clause [n, apos, bneg]
     return p
addPositively fm@(Ite g t e) = 
  do (p,n) <- freshELits
     gpos <- addPositively g
     gneg <- addNegatively g >>= negateELit
     tpos <- addPositively t
     epos <- addPositively e
     addLitClause $ Clause [n, gneg, tpos]
     addLitClause $ Clause [n, gpos, epos]
     return p
addPositively fm@(a `Imp` b) = 
  do (p,n) <- freshELits
     aneg <- addNegatively a >>= negateELit
     bpos <- addPositively b
     addLitClause $ Clause [n, aneg, bpos]
     return p
addPositively fm@(Neg a) = addNegatively a >>= negateELit
addPositively fm@(A _) = plit fm
addPositively Top = return TopLit
addPositively Bot = return BotLit

addNegatively :: (Eq l, Solver s l) => PropFormula l -> SatSolver s l (ExtLit l)
addNegatively fm@(And as) = 
  do (p,n) <- freshELits
     nlits <- mapM (\l -> addNegatively l >>= negateELit) as
     addLitClause $ Clause $ p:nlits
     return p
addNegatively fm@(Or as) = 
  do (p,n) <- freshELits
     nlits <- mapM (\l -> addNegatively l >>= negateELit) as
     mapM_ (\l -> addLitClause $ Clause [p, l]) nlits
     return p
addNegatively fm@(a `Iff` b) = 
  do (p,n) <- freshELits
     apos <- addPositively a
     aneg <- addNegatively a >>= negateELit
     bpos <- addPositively b
     bneg <- addNegatively b >>= negateELit
     addLitClause $ Clause [p, apos, bpos]
     addLitClause $ Clause [p, aneg, bneg]
     return p
addNegatively fm@(Ite g t e) = 
  do p <- freshELit 
     gpos <- addPositively g
     gneg <- addNegatively g >>= negateELit
     tneg <- addNegatively t >>= negateELit
     eneg <- addNegatively e >>= negateELit
     addLitClause $ Clause [p, gneg, tneg]
     addLitClause $ Clause [p, gpos, eneg]
     return p
addNegatively fm@(a `Imp` b) = 
  do p <- freshELit
     apos <- addPositively a
     bneg <- addNegatively b >>= negateELit
     addLitClause $ Clause [p, apos]
     addLitClause $ Clause [p, bneg]
     return p
addNegatively fm@(Neg a) = addPositively a >>= negateELit
addNegatively fm@(A _) = plit fm
addNegatively Top = return TopLit
addNegatively Bot = return BotLit

addFormula :: (Eq l, Solver s l) => PropFormula l -> SatSolver s l ()
addFormula fm = 
 do p <- addPositively fm
    addLitClause $ Clause [p]
    return ()

class Typeable a => Decoder e a | e -> a, a -> e where
  extract :: PA -> Maybe a
  extract (PA a) = cast a
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

constructValue :: (Decoder e a, Solver s l) => e -> SatSolver s l e
constructValue e = State.get >>= (liftS . Map.foldWithKey f (return e))
  where f atm v m = case extract atm of
                      Just a -> getModelValue v >>= \ val -> if val then add a `liftM` m else m
                      Nothing -> m

ifM :: Monad m =>  m Bool -> m a -> m a -> m a
ifM mc mt me = do c <- mc
                  if c then mt else me
run_ :: (Solver s l) => SatSolver s l r -> IO r
run_ (SatSolver m) = run $ State.evalStateT m Map.empty

value :: (Decoder e a, Solver s l) => SatSolver s l () -> e -> IO (Maybe e)
value m p = run_ $ m >> ifM (liftS solve) (Just `liftM` constructValue p) (return Nothing)
