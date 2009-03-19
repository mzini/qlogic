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
  -- * Conjunctive Normal Forms
  , CNF
  , top
  , bot
  , singleton
  , fromList
  , (+&+)
  , fold
  , isContradiction
  , fromFormula
  , clauseCount
  ) 
where
import Prelude hiding (foldr)
import qualified Data.List as List
import Qlogic.Formula (Formula(..), Atom)

data Literal = PosLit !Atom -- ^ positive literal
             | NegLit !Atom -- ^ negative literal
               deriving (Show, Eq, Ord)

-- | a clause is a sequence of 'Literal's
newtype Clause = Clause {clauseToList :: [Literal]} deriving Show

emptyClause :: Clause
-- ^ the empty 'Clause'
emptyClause = clause []

clause :: [Literal] -> Clause
clause = Clause 

-- | a Conjunctive Normal Form is a sequence of 'Clause's
data CNF = Empty
           | Singleton Clause
           | CNF :&: CNF deriving Show

isContradiction :: CNF -> Bool
isContradiction (Singleton (Clause [])) = True
isContradiction _                       = False

top :: CNF
-- ^ the empty set of clauses
top = Empty

bot :: CNF
-- ^ the singleton set containing the empty clause
bot = Singleton emptyClause

singleton :: Clause -> CNF
-- ^ the singleton set containing the empty clause
singleton = Singleton

fromList :: [Clause] -> CNF
-- ^ translate a 'List' of 'Clause's to a 'CNF'
fromList []     = Empty
fromList [a]    = Singleton a
fromList (a:as) = List.foldr (:&:) (Singleton a) $ map Singleton as

(+&+) :: CNF -> CNF -> CNF
-- ^ concatenation of two 'CNF's
Empty +&+ b     = b
a     +&+ Empty = a
a     +&+ b     = a :&: b

fold :: (Clause -> b -> b) -> b -> CNF -> b 
-- ^ folding over 'CNF's
fold _ b Empty           = b
fold f b (Singleton a)   = f a b
fold f b (cnf1 :&: cnf2) = fold f (fold f b cnf2) cnf1

clauseCount :: CNF -> Int
clauseCount Empty =  0
clauseCount (Singleton a) = 1
clauseCount (a :&: b) = clauseCount a + clauseCount b

fromFormula :: Formula -> CNF
-- ^ translate a 'Formula' into a 'CNF' with the possibly exponential textbook algorithm
fromFormula = cnf . nnf . implFree

implFree (a `Imp` b) = Neg (implFree a) `Or` implFree b
implFree (a `Or` b)  = implFree a `Or` implFree b
implFree (a `And` b) = implFree a `And` implFree b
implFree (a `Iff` b) = (Neg ifa `Or` ifb) `And` (ifa `Or` Neg ifb)
  where ifa = implFree a
        ifb = implFree b
implFree (Neg a)     = Neg $ implFree a
implFree x           = x

nnf (Neg (a `Or` b))  = nnf (Neg a) `And` nnf (Neg b)
nnf (Neg (a `And` b)) = nnf (Neg a) `Or` nnf (Neg b)
nnf (Neg (Neg a))     = nnf a
nnf (Neg Top)         = Bot
nnf (Neg Bot)         = Top
nnf (a `And` b)       = nnf a `And` nnf b
nnf (a `Or` b)        = nnf a `Or` nnf b
nnf a                 = a

cnf Top                = top
cnf Bot                = bot
cnf (a `And` b)        = cnf a +&+ cnf b
cnf (a `Or` b)         = distr (cnf a) (cnf b)
cnf (Neg (A a))     = singleton $ clause [NegLit a]
cnf (A a)           = singleton $ clause [PosLit a]

distr Empty _                     = Empty
distr _ Empty                     = Empty
distr (a :&: b) c                 = distr a c :&: distr b c 
distr a  (b :&: c)                = distr a b :&: distr a c
distr (Singleton a) (Singleton b) = singleton $ clause $ clauseToList a ++ clauseToList b
