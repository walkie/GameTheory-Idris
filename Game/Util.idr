module Game.Util

%default total


-- | Haskell's `Data.Function.on`.
on : (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g x y = f (g x) (g y)

-- | A version of `toList` with a more specific type.
toList' : Vect n a -> List a
toList' = toList
