module Util

-- | Haskell's Data.Function.on
on : (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g x y = f (g x) (g y)
