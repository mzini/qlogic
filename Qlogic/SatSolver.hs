{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
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
    , fix
    , value
    , freshLit
    , getAssign
    , runSolver
    , liftS
    , liftIO
    )
where

import System.IO.Unsafe (unsafePerformIO)

import Control.Monad
import Control.Monad.Trans (lift, liftIO, MonadIO)
import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import qualified Qlogic.Assign as Assign
import Qlogic.Assign (Assign, (|->))
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

data ExtLit l = Lit !l | TopLit | BotLit deriving (Eq, Show)

data Polarity = PosPol | NegPol

newtype SatSolver s l r = SatSolver (State.StateT (Map.Map PA l) s r)
    deriving (Monad, StateClass.MonadState (Map.Map PA l), MonadIO)

liftS :: Solver s l => s r -> SatSolver s l r 
liftS = SatSolver . lift

freshLit :: Solver s l => SatSolver s l l
freshLit = liftS newLit

freshELit :: Solver s l => SatSolver s l (ExtLit l)
freshELit = Lit `liftM` freshLit

atomToELit :: Solver s l => PA -> SatSolver s l (ExtLit l)
atomToELit a = do litMap <- State.get
                  case Map.lookup a litMap of
                    Just oldLit -> return $ Lit oldLit
                    Nothing     -> do l <- freshLit
                                      State.put $ Map.insert a l litMap
                                      return (Lit l)

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
addPositively fm@(Neg a) = addNegatively a >>= negateELit
addPositively fm@(A _)   = plit fm
addPositively fm@(SL l)  = plit fm
addPositively Top        = return TopLit
addPositively Bot        = return BotLit
addPositively fm         = do (p,n) <- freshELits 
                              addPositively' (p,n) fm

addPositively' :: (Eq l, Solver s l) => (ExtLit l,ExtLit l) -> PropFormula l -> SatSolver s l (ExtLit l)
addPositively' (p,n) fm@(And as) =
  do plits <- mapM addPositively as
     mapM_ (\l -> addLitClause $ Clause [n, l]) plits
     return p
addPositively' (p,n) fm@(Or as) =
  do plits <- mapM addPositively as
     addLitClause $ Clause $ n:plits
     return p
addPositively' (p,n) fm@(a `Iff` b) =
  do apos <- addPositively a
     aneg <- addNegatively a >>= negateELit
     bpos <- addPositively b
     bneg <- addNegatively b >>= negateELit
     addLitClause $ Clause [n, aneg, bpos]
     addLitClause $ Clause [n, apos, bneg]
     return p
addPositively' (p,n) fm@(Ite g t e) =
  do gpos <- addPositively g
     gneg <- addNegatively g >>= negateELit
     tpos <- addPositively t
     epos <- addPositively e
     addLitClause $ Clause [n, gneg, tpos]
     addLitClause $ Clause [n, gpos, epos]
     return p
addPositively' (p,n) fm@(a `Imp` b) =
  do aneg <- addNegatively a >>= negateELit
     bpos <- addPositively b
     addLitClause $ Clause [n, aneg, bpos]
     return p
addPositively' (p,n) fm@(Neg a) = do addNegatively' (n,p) a
                                     return p
addPositively' (p,n) fm@(A _)   = do l <- plit fm
                                     addLitClause $ Clause [n, l]
                                     return l
addPositively' (_,n) fm@(SL l)  = do l <- plit fm
                                     addLitClause $ Clause [n, l]
                                     return l
addPositively' (_,_) Top        = return TopLit
addPositively' (_,n) Bot        = addLitClause (Clause [n]) >> return BotLit


addNegatively :: (Eq l, Solver s l) => PropFormula l -> SatSolver s l (ExtLit l)
addNegatively fm@(Neg a) = addPositively a >>= negateELit
addNegatively fm@(A _)   = plit fm
addNegatively fm@(SL l)  = plit fm
addNegatively Top        = return TopLit
addNegatively Bot        = return BotLit
addNegatively fm         = do (p,n) <- freshELits
                              addNegatively' (p,n) fm

addNegatively' :: (Eq l, Solver s l) => (ExtLit l, ExtLit l) -> PropFormula l -> SatSolver s l (ExtLit l)
addNegatively' (p,n) fm@(And as) =
  do nlits <- mapM (\l -> addNegatively l >>= negateELit) as
     addLitClause $ Clause $ p:nlits
     return p
addNegatively' (p,n) fm@(Or as) = 
  do nlits <- mapM (\l -> addNegatively l >>= negateELit) as
     mapM_ (\l -> addLitClause $ Clause [p, l]) nlits
     return p
addNegatively' (p,n) fm@(a `Iff` b) =
  do apos <- addPositively a
     aneg <- addNegatively a >>= negateELit
     bpos <- addPositively b
     bneg <- addNegatively b >>= negateELit
     addLitClause $ Clause [p, apos, bpos]
     addLitClause $ Clause [p, aneg, bneg]
     return p
addNegatively' (p,n) fm@(Ite g t e) =
  do gpos <- addPositively g
     gneg <- addNegatively g >>= negateELit
     tneg <- addNegatively t >>= negateELit
     eneg <- addNegatively e >>= negateELit
     addLitClause $ Clause [p, gneg, tneg]
     addLitClause $ Clause [p, gpos, eneg]
     return p
addNegatively' (p,n) fm@(a `Imp` b) =
  do apos <- addPositively a
     bneg <- addNegatively b >>= negateELit
     addLitClause $ Clause [p, apos]
     addLitClause $ Clause [p, bneg]
     return p
addNegatively' (p,n) fm@(Neg a)  = do addPositively' (n,p) a
                                      return p
addNegatively' (p,n) fm@(A _)    = do l' <- plit fm >>= negateELit
                                      addLitClause $ Clause [l',p]
                                      return n
addNegatively' (p,n) fm@(SL l)   = do l' <- plit fm >>= negateELit
                                      addLitClause $ Clause [l',p]
                                      return n
addNegatively' (p,_) Top         = addLitClause (Clause [p]) >> return TopLit
addNegatively' (_,n) Bot         = return BotLit


addFormula :: (Show l, Eq l, Solver s l) => PropFormula l -> SatSolver s l ()
addFormula fm =
-- unsafePerformIO $ do putStrLn $ show fm
--                     return $
  do p <- addPositively fm
     addLitClause $ Clause [p]
     return ()

fix :: (Eq l, Solver s l) => l -> PropFormula l -> SatSolver s l ()
fix l fm = do n <- negateELit elit
              addPositively' (elit,n) fm
              addNegatively' (elit,n) fm
              return ()
--              unsafePerformIO ((putStrLn $ show l ++ " := " ++ show fm) >> (return $ return ()))
    where elit = Lit l

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

getAssign :: (Ord l, Solver s l) => SatSolver s l (Assign l)
getAssign = State.get >>= Map.foldWithKey f (return Assign.empty)
    where f k l m  = do assign <- m
                        v <- liftS $ getModelValue l
                        return $ Assign.add [Right k |-> v] assign

ifM :: Monad m =>  m Bool -> m a -> m a -> m a
ifM mc mt me = do c <- mc
                  if c then mt else me

runSolver :: (Solver s l) => SatSolver s l r -> IO r
runSolver (SatSolver m) = run $ State.evalStateT m Map.empty



value :: (Decoder e a, Solver s l) => SatSolver s l () -> e -> IO (Maybe e)
value m p = runSolver $ m >> ifM (liftS solve) (Just `liftM` constructValue p) (return Nothing)
