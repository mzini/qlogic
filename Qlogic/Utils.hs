module Qlogic.Utils where

class ShowLimit a where
  showlimit :: Int -> a -> String

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
