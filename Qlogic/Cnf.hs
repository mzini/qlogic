{-# LANGUAGE TypeSynonymInstances #-}
module Qlogic.Cnf
  ( -- * Types 
   Literal(..)
  , Clause
  , CNF
  -- * Operations
  , isVarLit
  , emptyClause
  , empty
  , (+&+)
  , fromList
  ) 
where
import qualified Data.Sequence as Seq
import Data.Sequence ((><))
import Data.Foldable

data Literal a = PosLit a -- ^ positive literal
               | NegLit a -- ^ negative literal
               | TopLit 
               | BotLit
                 deriving (Show, Eq)

type Clause a = [Literal a]

type CNF a = Seq.Seq (Clause a)

empty :: CNF a
-- ^ the empty 'CNF'
empty = Seq.empty

emptyClause :: Clause a
-- ^ the empty 'Clause'
emptyClause = []

(+&+) :: CNF a -> CNF a -> CNF a
-- ^ concatenation of two 'CNF's
(+&+) = (><)

isVarLit :: Literal a -> Bool
-- ^ Returns 'True' if the given literal is either 
--   a positive or negative variable
isVarLit (PosLit _) = True
isVarLit (NegLit _) = True
isVarLit _ = False

fromList :: [Clause a] -> CNF a
fromList = Seq.fromList

