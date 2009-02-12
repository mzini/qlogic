{-# LANGUAGE TypeSynonymInstances #-}
module Qlogic.Assign where
import qualified Data.Map as Map
import qualified Data.List as List
import Control.Monad (join)
type Assign a = Map.Map a (Maybe Bool)

type Binding a = (a,Maybe Bool)

lookup :: Ord a => a -> Assign a -> Maybe Bool 
lookup a ass = join $ Map.lookup a ass

(|->) :: a -> Maybe Bool -> Binding a
a |-> b = (a,b)

empty :: Assign a
empty = Map.empty

bind :: Ord a => [Binding a] -> Assign a -> Assign a
bind bs ass = List.foldl insert ass bs
    where insert ass' (a,b) = Map.insert a b ass'

-- instance Show a => Show (Assign a) where 
--     show assign = wrap $ concatMap (\(k,v) -> show k ++ "|->" ++ show v) $ Map.toList assign 
--         where wrap a = "{" ++ a ++ "}"