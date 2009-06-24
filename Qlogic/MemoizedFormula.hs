{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Qlogic.MemoizedFormula 
    ( toFormula 
    , memoized
    , MemoFormula)
where 

import Qlogic.SatSolver
import Qlogic.Formula 
import Qlogic.Boolean
import Qlogic.PropositionalFormula
import Qlogic.SatSolver 
import Control.Monad
import qualified Sat as Sat
import qualified Control.Monad.State.Lazy as State
import Control.Monad.Trans (lift)
import qualified Data.Map as Map
import Prelude hiding ((&&),(||),not,foldl,foldr)

data ASt l = IsTop
           | IsBot
           | IsAtom PA 
           | IsLit l
           | IsFmt l

type Cache arg l = Map.Map arg (ASt l)

data MemoState arg l = St {
      conjs :: [PropFormula l]
    , cache :: Cache arg l
    }

type Memo arg s l r = State.StateT (MemoState arg l) (SatSolver s l) r
type MemoFormula arg s l = Memo arg s l (PropFormula l)

initialState :: MemoState arg l
initialState = St [] Map.empty

modifyCache :: Monad s => (Cache arg l -> Cache arg l) -> Memo arg s l ()
modifyCache f = State.modify $ \ st -> st { cache = f (cache st)}

getCache :: Monad s => Memo arg s l (Cache arg l)
getCache = cache `liftM` State.get

addConj :: Monad s => PropFormula l -> Memo args s l ()
addConj fm = State.modify $ \ st -> st { conjs = fm : conjs st}

toFormula :: (Solver s l, Eq l) => MemoFormula arg s l -> SatSolver s l (PropFormula l)
toFormula fm = do (f, st) <- State.runStateT fm initialState
                  return $ f && (bigAnd $ conjs st)

memoized :: (Solver s l, Ord arg, Eq l) => 
           (arg -> MemoFormula arg s l) -> arg -> MemoFormula arg s l
memoized f arg = do c <- getCache
                    fm <- f arg
                    newASt <- mkASt fm
                    case Map.insertLookupWithKey (\ _ _ oldASt -> oldASt) arg newASt c of
                      (Just oldASt, _   ) -> return $ fml oldASt
                      (Nothing    , newC) -> modifyCache (const newC) >> maybeAddConj newASt fm >> return (fml newASt)
    where maybeAddConj (IsFmt l) fm = addConj $ literal l --> fm
          maybeAddConj _         _  = return ()
          mkASt Top    = return IsTop
          mkASt Bot    = return IsBot
          mkASt (A a)  = return $ IsAtom a
          mkASt (SL l) = return $ IsLit l
          mkASt fm     = do l <- lift freshLit 
                            return $ IsFmt l
          fml IsTop      = Top
          fml IsBot      = Bot
          fml (IsAtom a) = atom a
          fml (IsFmt f ) = literal f


instance (Monad s, Eq l) => Boolean (MemoFormula arg s l) where
    (&&) = liftM2 (&&)
    (||) = liftM2 (||)
    not = liftM not
    top = return top
    bot = return bot
    (<->) = liftM2 (<->)
    (-->) = liftM2 (-->)
    ite = liftM3 ite
                                                         
    
