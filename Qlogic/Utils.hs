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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Qlogic.Utils where

class ShowLimit a where
  showlimit :: Int -> a -> String

instance Show a => ShowLimit a where
  showlimit n _ | n <= 0 = ""
  showlimit n a          = show a

instance (ShowLimit a, ShowLimit b) => ShowLimit (a, b) where
  showlimit n _ | n <= 0 = ""
  showlimit n (a, b)     = "(" ++ showlimit (n - 1) a ++ ", " ++ showlimit (n - 1) b ++ ")"

instance (ShowLimit a, ShowLimit b, ShowLimit c) => ShowLimit (a, b, c) where
  showlimit n _ | n <= 0 = ""
  showlimit n (a, b, c)  = "(" ++ showlimit (n - 1) a ++ ", " ++ showlimit (n - 1) b ++ ", " ++ showlimit (n - 1) c ++ ")"

instance ShowLimit a => ShowLimit [a] where
  showlimit n _ | n <= 0 = ""
  showlimit n []         = "[]"
  showlimit n xs         = "[" ++ showlimit (n - 1) (head xs) ++ foldr (\a s -> ", " ++ showlimit (n - 1) a ++ s) "]" (tail xs)

instance ShowLimit Bool where
  showlimit n _ | n <= 0 = ""
  showlimit _ True       = "True"
  showlimit _ False      = "False"

instance ShowLimit Int where
  showlimit n _ | n <= 0 = ""
  showlimit _ n          = show n
