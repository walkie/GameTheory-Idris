-- | Vectors where each element corresponds to a game instance.
module Game.ByGame

import Data.VectBy

%default total


--
-- * Game IDs
--

-- | Identifies a game instance within an execution.
--   Construct using the `toGameID` or `game` functions.
data GameID : Nat -> Type where
  MkGameID : Fin n -> GameID n

-- | Construct a `GameID` from an int

-- | Construct a `GameID` from an integer from n to 1, where n is the
--   number of game instances executed so far.
toGameID : Integer -> Maybe (GameID n)
toGameID {n} i = map MkGameID (integerToFin (cast n - i) n)

-- | Construct a `GameID` from an integer that is statically ensured to be
--   within range.
game : (i : Integer) -> {default ItIsJust p : IsJust (toGameID {n} i)} -> GameID n
game {n} i {p} with (toGameID {n} i)
  game {n} i {p = ItIsJust} | Just x = x

instance Eq (GameID n) where
  (MkGameID f) == (MkGameID f') = f == f'
instance Show (GameID n) where
  show (MkGameID f) = "Game " ++ show (cast n - finToInteger f)
instance Cast (GameID n) (Fin n) where
  cast (MkGameID f) = f


--
-- * ByGame vectors
--

-- | A vector where each element corresponds to a game instance.
--   A `ByGame` vector of length n is indexed from n down to 1.
ByGame : Nat -> Type -> Type
ByGame = VectBy GameID

-- | Add an element corresponding to a new game instance.
addGame : a -> ByGame n a -> ByGame (S n) a
addGame a (MkVectBy as) = MkVectBy (a :: as)

--
-- * Static unit tests
--

test_toGameID :
  so (toGameID {n=3} (-1) == Nothing
   && toGameID {n=3} 0    == Nothing
   && toGameID {n=0} 1    == Nothing
   && toGameID {n=1} 1    == Just (MkGameID 0)
   && toGameID {n=2} 1    == Just (MkGameID 1)
   && toGameID {n=3} 1    == Just (MkGameID 2)
   && toGameID {n=2} 2    == Just (MkGameID 0)
   && toGameID {n=3} 2    == Just (MkGameID 1)
   && toGameID {n=3} 3    == Just (MkGameID 0)
   && toGameID {n=3} 4    == Nothing)
test_toGameID = oh

test_game :
  so (game {n=1} 1 == MkGameID 0
   && game {n=2} 1 == MkGameID 1
   && game {n=3} 1 == MkGameID 2
   && game {n=2} 2 == MkGameID 0
   && game {n=3} 2 == MkGameID 1
   && game {n=3} 3 == MkGameID 0)
test_game = oh

test_forGame :
  so (for (game 1) [7,8,9] == 9
   && for (game 2) [7,8,9] == 8
   && for (game 3) [7,8,9] == 7)
test_forGame = oh
