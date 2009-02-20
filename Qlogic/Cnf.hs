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
  , foldr
  , isContradiction
  , fromFormula
  ) 
where
import Prelude hiding (foldr)
import qualified Data.List as List
import Qlogic.Formula (Formula(..))

data Literal a = PosLit a -- ^ positive literal
               | NegLit a -- ^ negative literal
                 deriving (Show, Eq)

-- | a clause is a sequence of 'Literal's
newtype Clause a = Clause {clauseToList :: [Literal a]}

emptyClause :: Clause a
-- ^ the empty 'Clause'
emptyClause = clause []

clause :: [Literal a] -> Clause a
clause = Clause 

-- | a Conjunctive Normal Form is a sequence of 'Clause's
data CNF a = Empty
           | Singleton (Clause a)
           | (CNF a) :&: (CNF a)

isContradiction :: CNF a -> Bool
isContradiction (Singleton (Clause [])) = True
isContradiction _                       = False

top :: CNF a
-- ^ the empty set of clauses
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
-- ^ folding over 'CNF's
foldr _ b Empty           = b
foldr f b (Singleton a)   = f a b
foldr f b (cnf1 :&: cnf2) = foldr f (foldr f b cnf2) cnf1

fromFormula :: Formula a -> CNF a
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
cnf (Neg (Atom a))     = singleton $ clause $ [NegLit a]
cnf (Atom a)           = singleton $ clause $ [PosLit a]

distr Empty _                     = Empty
distr _ Empty                     = Empty
distr (a :&: b) c                 = distr a c :&: distr b c 
distr a  (b :&: c)                = distr a b :&: distr a c
distr (Singleton a) (Singleton b) = singleton $ clause $ clauseToList a ++ clauseToList b
