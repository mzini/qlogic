module Qlogic.Assign where
import qualified Data.Map as Map
import qualified Data.List as List
import Control.Monad (join)

type Assign a = Map.Map a Bool

type Binding a = (a, Bool)

lookup :: Ord a => a -> Assign a -> Maybe Bool
lookup = Map.lookup

(|->) :: a -> Bool -> Binding a
a |-> b = (a,b)

empty :: Assign a
empty = Map.empty

bind :: Ord a => [Binding a] -> Assign a -> Assign a
bind bs ass = List.foldl insert ass bs
    where insert ass' (a,b) = Map.insert a b ass'

fromMap :: Map.Map a Bool -> Assign a
fromMap = id

toMap :: Assign a -> Map.Map a Bool
toMap = id
