{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Qlogic.Cnf
  (-- * Literals
   Literal(..) 
   -- * Clauses 
  , Clause
  , emptyClause
  , clause 
  , clauseToList
  -- * Conjunctive Normal Form
  , CNF
  , top
  , bot
  , singleton
  , fromList
  , (+&+)
  , foldr
  , isContradiction
  ) 
where
import Prelude hiding (foldr)
import qualified Data.List as List

data Literal a = PosLit a -- ^ positive literal
               | NegLit a -- ^ negative literal
                 deriving (Show, Eq)

newtype Clause a = Clause {clauseToList :: [Literal a]}

emptyClause :: Clause a
-- ^ the empty 'Clause'
emptyClause = clause []

clause :: [Literal a] -> Clause a
clause = Clause 

data CNF a = Empty
           | Singleton (Clause a)
           | (CNF a) :&: (CNF a)

isContradiction :: CNF a -> Bool
isContradiction (Singleton (Clause [])) = True
isContradiction _                       = False

top :: CNF a
-- ^ the empty set of clausse
top = Empty

bot :: CNF a
-- ^ the singleton set containing the empty clause
bot = Singleton emptyClause

singleton :: Clause a -> CNF a
-- ^ the singleton set containing the empty clause
singleton = Singleton



fromList :: [Clause a] -> CNF a
-- ^ translate a 'List' of 'Clause's to a 'CNF'
fromList []     = Empty
fromList [a]    = Singleton a
fromList (a:as) = List.foldr (:&:) (Singleton a) $ map Singleton as

(+&+) :: CNF a -> CNF a -> CNF a
-- ^ concatenation of two 'CNF's
Empty +&+ b     = b
a     +&+ Empty = a
a     +&+ b     = a :&: b

foldr :: (Clause a -> b -> b) -> b -> CNF a -> b 
foldr _ b Empty           = b
foldr f b (Singleton a)   = f a b
foldr f b (cnf1 :&: cnf2) = foldr f (foldr f b cnf2) cnf1


