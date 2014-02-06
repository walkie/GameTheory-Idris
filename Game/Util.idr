module Game.Util

-- | Convert a Nat into a Fin, using zero on failure.
natToFin_ : Nat -> Fin (S n)
natToFin_ j {n} = fromMaybe fZ (natToFin j (S n))

-- | Haskell's Data.Function.on
on : (b -> b -> c) -> (a -> b) -> a -> a -> c
on f g x y = f (g x) (g y)
