{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Qlogic.MiniSat 
 ( solve
 , solveCnf
 , Decoder(..)
 , MiniSat
 , addFormula
 , addClauses
 , value
 , (:&:) (..)
 , constructValue
 )

where 
import qualified Control.Monad.State.Lazy as State
import qualified Data.Map as Map
import Prelude hiding (mapM_)
import Control.Monad (liftM,mapM)
import Data.Foldable (mapM_)
import Control.Monad.Trans (lift)
import qualified Sat as Sat
import qualified Qlogic.Assign as Assign
import Data.Typeable 

import Qlogic.Formula
import Qlogic.Cnf (Literal(..))
import qualified Qlogic.Cnf as Cnf
import Qlogic.Assign ((|->), Assign)
import qualified Qlogic.Tseitin as Tseitin

type AtomMap = Map.Map PropositionalAtom Sat.Lit

type MiniSat r = State.StateT AtomMap Sat.S r

newLit :: MiniSat Sat.Lit
newLit = lift Sat.newLit

literal :: PropositionalAtom -> MiniSat Sat.Lit
literal a =
  do n <- newLit
     literals  <- State.get
     case Map.insertLookupWithKey f a n literals of
       (Nothing, m) -> State.modify (const m) >> return n
       (Just b, _)  -> return b
     where f key newV oldV = oldV

getModelValue :: Sat.Lit -> MiniSat Bool
getModelValue v = lift $ Sat.getModelValue v

addClauses :: Cnf.CNF PropositionalAtom -> MiniSat ()
addClauses cnf | Cnf.isContradiction cnf = lift Sat.contradiction
               | otherwise               = Cnf.fold f (return ()) cnf
  where f clause m = do mlits <- mapM mkLit $ Cnf.clauseToList clause
                        lift $ Sat.addClause mlits
                        m
        mkLit (PosLit l) = literal l
        mkLit (NegLit l) = Sat.neg `liftM` literal l

-- addClauses :: Cnf.CNF CInt -> MiniSat ()
-- addClauses cnf | Cnf.isContradiction cnf = lift Sat.contradiction
--                | otherwise               = Cnf.fold f (return ()) cnf
--   where f clause m = do mlits <- mapM mkLit $ Cnf.clauseToList clause
--                         lift $ Sat.addClause mlits
--                         m
--         mkLit (PosLit l) = altliteral l
--         mkLit (NegLit l) = Sat.neg `liftM` altliteral l
--         altliteral = undefined

addFormula :: PropositionalFormula -> MiniSat ()
addFormula fm = addClauses $ Tseitin.transform fm

extractAssign :: MiniSat Assign
extractAssign = State.get >>= Map.foldWithKey f (return Assign.empty)
    where f k l m | Tseitin.isFormulaAtom k = m
                  | otherwise               = do assign <- m
                                                 v <- getModelValue l
                                                 return $ Assign.add [k |-> v] assign

run :: MiniSat r -> IO r
run m = Sat.run $ State.evalStateT m Map.empty


solve :: PropositionalFormula -> IO (Maybe Assign)
solve fm = run $ solve_ $ Tseitin.transform fm

solveCnf :: Cnf.CNF PropositionalAtom -> IO (Maybe Assign)
solveCnf = run . solve_

solve_ :: Cnf.CNF PropositionalAtom -> MiniSat (Maybe Assign)
solve_ cnf = do addClauses cnf
                isSat <- lift $ Sat.solve []
                case isSat of 
                  True -> Just `liftM` extractAssign
                  False -> return Nothing



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

constructValue :: (Decoder e a) => e -> MiniSat e
constructValue e = State.get >>= Map.foldWithKey f (return $ e)
  where f a v m = case extract a of
                    Just a' -> getModelValue v >>= \ val -> if val then add a' `liftM` m else m
                    Nothing -> m

ifM :: Monad m =>  m Bool -> m a -> m a -> m a
ifM mc mt me = do c <- mc
                  if c then mt else me

value :: (Decoder e a) => MiniSat () -> e -> IO (Maybe e)
value m p = run $ m >> ifM (lift $ Sat.solve []) (Just `liftM` constructValue p) (return Nothing)



