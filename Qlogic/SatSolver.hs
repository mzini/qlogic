{-
This file is part of the Haskell Qlogic Library.

The Haskell Qlogic Library is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

The Haskell Qlogic Library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with the Haskell Qlogic Library.  If not, see <http://www.gnu.org/licenses/>.
-}

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
    , SatError (..)
    , (:&:) (..)
    , addFormula
    , fix
    , value
    , assignment
    , checkFormula
    , freshLit
    , getAssign
    , runSolver
    , liftS
    , liftIO
    )
where

import Control.Monad
import Control.Monad.Trans (lift, liftIO, MonadIO)
import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Qlogic.Assign as Assign
import Qlogic.Assign (Assign, (|->))
import Data.Typeable
import qualified Control.Monad.State.Class as StateClass
import Prelude hiding (negate)

import Qlogic.Formula
import Control.Monad.Error hiding (fix)
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

data State l = State { litMap :: Map.Map PA l
                     , assertedFms :: [PropFormula l] }

data SatError = Unsatisfiable 
              | AssertFailed
              | OtherError String

instance Error SatError where 
    strMsg = OtherError

newtype SatSolver s l r = SatSolver (ErrorT SatError (State.StateT (State l) s) r)
    deriving (Monad, StateClass.MonadState (State l), MonadIO, MonadError SatError)

liftS :: Solver s l => s r -> SatSolver s l r 
liftS = SatSolver . lift . lift


runSolver :: (Solver s l) => SatSolver s l r -> IO (Either SatError r)
runSolver (SatSolver m) = run $ State.evalStateT (runErrorT m) $ State Map.empty []

freshLit :: Solver s l => SatSolver s l l
freshLit = liftS newLit

freshELit :: Solver s l => SatSolver s l (ExtLit l)
freshELit = Lit `liftM` freshLit

getLitMap :: (Solver s l) => SatSolver s l (Map.Map PA l)
getLitMap = litMap `liftM` State.get

putLitMap :: (Solver s l) => (Map.Map PA l) -> SatSolver s l ()
putLitMap lm = State.modify (\s -> s{litMap = lm})


atomToELit :: Solver s l => PA -> SatSolver s l (ExtLit l)
atomToELit a = Lit `liftM` atomToLit a

atomToLit :: Solver s l => PA -> SatSolver s l l
atomToLit a = do lm <- getLitMap
                 case Map.lookup a lm of 
                    Just oldLit -> return oldLit
                    Nothing     -> do {l <- freshLit;
                                      putLitMap (Map.insert a l lm);
                                      return l}

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

fmToClauses :: (Eq l, Solver s l) => PropFormula l -> SatSolver s l (Maybe [Clause (ExtLit l)])
fmToClauses (And as)    = do cs <- mapM fmToClauses as
                             if all Maybe.isJust cs then return $ Just $ concat $ Maybe.catMaybes cs else return Nothing
fmToClauses (Or [])     = return $ Just [Clause []]
fmToClauses (Or [a])    = fmToClauses a
fmToClauses fm@(Or _)   = do ac <- fmToClause fm
                             case ac of
                               Nothing  -> return Nothing
                               Just ac' -> return $ Just [ac']
fmToClauses (a `Iff` b) = fmToClauses (And [Or [Neg a, b], Or [a, Neg b]])
fmToClauses (Ite g t e) = fmToClauses (And [Or [Neg g, t], Or [g, e]])
fmToClauses (a `Imp` b) = do ac <- fmToClause (Or [Neg a, b])
                             case ac of
                               Nothing  -> return Nothing
                               Just ac' -> return $ Just [ac']
fmToClauses (Maj a b c) = fmToClauses (And [Or [a, b], Or [a, c], Or [b, c]])
fmToClauses (Neg a)     = negFmToClauses a
fmToClauses fm@(A _)    = do al <- plit fm
                             return $ Just [Clause [al]]
fmToClauses fm@(SL _)   = do al <- plit fm
                             return $ Just [Clause [al]]
fmToClauses Top         = return $ Just []
fmToClauses Bot         = return $ Just [Clause []]

fmToClause :: (Eq l, Solver s l) => PropFormula l -> SatSolver s l (Maybe (Clause (ExtLit l)))
fmToClause (And [])    = return $ Just (Clause [TopLit])
fmToClause (And [a])   = fmToClause a
fmToClause (And _)     = return Nothing
fmToClause (Or as)     = do cs <- mapM fmToClause as
                            if all Maybe.isJust cs then return $ Just $ Clause $ concatMap clauseToList $ Maybe.catMaybes cs else return Nothing
fmToClause (_ `Iff` _) = return Nothing
fmToClause (Ite _ _ _) = return Nothing
fmToClause (a `Imp` b) = fmToClause (Or [Neg a, b])
fmToClause (Maj _ _ _) = return Nothing
fmToClause (Neg a)     = negFmToClause a
fmToClause fm@(A _)    = do al <- plit fm
                            return $ Just $ Clause [al]
fmToClause fm@(SL _)   = do al <- plit fm
                            return $ Just $ Clause [al]
fmToClause Top         = return $ Just $ Clause [TopLit]
fmToClause Bot         = return $ Just $ Clause []

negFmToClauses :: (Eq l, Solver s l) => PropFormula l -> SatSolver s l (Maybe [Clause (ExtLit l)])
negFmToClauses (And [])    = return $ Just [Clause []]
negFmToClauses (And [a])   = negFmToClauses a
negFmToClauses fm@(And _)  = do ac <- negFmToClause fm
                                case ac of
                                  Nothing  -> return Nothing
                                  Just ac' -> return $ Just [ac']
negFmToClauses (Or as)     = do cs <- mapM negFmToClauses as
                                if all Maybe.isJust cs then return $ Just $ concat $ Maybe.catMaybes cs else return Nothing
negFmToClauses (a `Iff` b) = fmToClauses (And [Or [Neg a, Neg b], Or [a, b]])
negFmToClauses (Ite g t e) = negFmToClauses (Or [And [g, t], And [Neg g, e]])
negFmToClauses (a `Imp` b) = fmToClauses (And [a, Neg b])
negFmToClauses (Maj a b c) = fmToClauses (And [Or [Neg a, Neg b], Or [Neg a, Neg c], Or [Neg b, Neg c]])
negFmToClauses (Neg a)     = fmToClauses a
negFmToClauses fm@(A _)    = do al <- plit $ Neg fm
                                return $ Just $ [Clause [al]]
negFmToClauses fm@(SL _)   = do al <- plit $ Neg fm
                                return $ Just $ [Clause [al]]
negFmToClauses Top         = return $ Just $ [Clause []]
negFmToClauses Bot         = return $ Just $ []

negFmToClause :: (Eq l, Solver s l) => PropFormula l -> SatSolver s l (Maybe (Clause (ExtLit l)))
negFmToClause (And as)    = do cs <- mapM negFmToClause as
                               if all Maybe.isJust cs then return $ Just $ Clause $ concatMap clauseToList $ Maybe.catMaybes cs else return Nothing
negFmToClause (Or [])     = return $ Just (Clause [TopLit])
negFmToClause (Or [a])    = negFmToClause a
negFmToClause (Or _)      = return Nothing
negFmToClause (_ `Iff` _) = return Nothing
negFmToClause (Ite _ _ _) = return Nothing
negFmToClause (_ `Imp` _) = return Nothing
negFmToClause (Maj _ _ _) = return Nothing
negFmToClause (Neg a)     = fmToClause a
negFmToClause fm@(A _)    = do al <- plit $ Neg fm
                               return $ Just $ Clause [al]
negFmToClause fm@(SL _)   = do al <- plit $ Neg fm
                               return $ Just $ Clause [al]
negFmToClause Top         = return $ Just $ Clause []
negFmToClause Bot         = return $ Just $ Clause [TopLit]

addPositively :: (Eq l, Solver s l) => PropFormula l -> SatSolver s l (ExtLit l)
addPositively fm@(Neg a) = addNegatively a >>= negateELit
addPositively fm@(A _)   = plit fm
addPositively fm@(SL l)  = plit fm
addPositively Top        = return TopLit
addPositively Bot        = return BotLit
addPositively fm         = case isCnf fm of
                             True  -> do (p,n) <- freshELits
                                         cs <- liftM Maybe.fromJust $ fmToClauses fm
                                         mapM_ (\(Clause c) -> addLitClause $ Clause $ n:c) cs
                                         return p
                             False -> do (p,n) <- freshELits
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
addPositively' (p,n) fm@(Maj a b c) = do apos <- addPositively a
                                         bpos <- addPositively b
                                         cpos <- addPositively c
                                         addLitClause $ Clause [n, apos, bpos]
                                         addLitClause $ Clause [n, apos, cpos]
                                         addLitClause $ Clause [n, bpos, cpos]
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
addNegatively fm         = case isNegCnf fm of
                             True  -> do (p,_) <- freshELits
                                         cs <- liftM Maybe.fromJust $ negFmToClauses fm
                                         mapM_ (\(Clause c) -> addLitClause $ Clause $ p:c) cs
                                         return p
                             False -> do (p,n) <- freshELits
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
addNegatively' (p,_) fm@(Maj a b c) = do aneg <- addNegatively a >>= negateELit
                                         bneg <- addNegatively b >>= negateELit
                                         cneg <- addNegatively c >>= negateELit
                                         addLitClause $ Clause [p, aneg, bneg]
                                         addLitClause $ Clause [p, aneg, cneg]
                                         addLitClause $ Clause [p, bneg, cneg]
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
  do p <- addPositively fm
     addLitClause $ Clause [p]
     return ()

fix :: (Eq l, Solver s l) => l -> PropFormula l -> SatSolver s l ()
fix l fm = do n <- negateELit elit
              addPositively' (elit,n) fm
              addNegatively' (elit,n) fm
              return ()
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
constructValue e = getLitMap >>= (liftS . Map.foldWithKey f (return e))
  where f atm v m = case extract atm of
                      Just a -> getModelValue v >>= \ val -> if val then add a `liftM` m else m
                      Nothing -> m

getAssign :: (Ord l, Solver s l) => SatSolver s l (Assign l)
getAssign = getLitMap >>= Map.foldWithKey f (return Assign.empty)
    where f k l m  = do assign <- m
                        v <- liftS $ getModelValue l
                        return $ Assign.add [Right k |-> v] assign


checkFormula :: (Solver s l) => PropFormula l -> SatSolver s l ()
checkFormula fm = State.modify (\s -> s{assertedFms = fm : assertedFms s})


ifM :: Monad m =>  m Bool -> m a -> m a -> m a
ifM mc mt me = do c <- mc
                  if c then mt else me

assertFormula :: (Solver s l) => PropFormula l -> SatSolver s l ()
assertFormula fm = do r <- eval fm
                      if r then return () else throwError AssertFailed
    where eval (A a)        = do l <- atomToLit a 
                                 liftS $ getModelValue l 
          eval (SL a)       = liftS $ getModelValue a
          eval (And l)      = all id `liftM` mapM eval l
          eval (Or l)       = any id `liftM` mapM eval l
          eval (a `Iff` b)  = do r <- eval a 
                                 s <- eval b
                                 return $ r == s
          eval (a `Imp` b)  = do r <- eval a 
                                 s <- eval b
                                 return $ (not r) || s
          eval (Neg a)      = not `liftM` eval a
          eval Top          = return True
          eval Bot          = return False
          eval (Ite a b c)  = do g <- eval a 
                                 if g then eval b else eval c
          eval (Maj a b c)  = do r <- eval a
                                 s <- eval b
                                 t <- eval c
                                 return $ (r && s) || (r && t) || (s && t)


solveAndCheck :: (Ord l, Solver s l) => SatSolver s l ()
solveAndCheck = ifM (liftS solve)
                (assertedFms `liftM` State.get >>= mapM_ assertFormula)
                (throwError Unsatisfiable)

value :: (Ord l, Decoder e a, Solver s l) => SatSolver s l () -> e -> IO (Either SatError e)
value m p = runSolver $ m >> solveAndCheck >> constructValue p

assignment :: (Ord l, Solver s l) => SatSolver s l () -> IO (Either SatError (Assign l))
assignment m = runSolver $ m >> solveAndCheck >> getAssign

