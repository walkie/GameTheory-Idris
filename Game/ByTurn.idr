-- | Vectors where each element corresponds to a turn in a game instance.
module Game.ByTurn

import Data.VectBy

%default total


--
-- * Turn IDs
--

-- | Identifies a turn within a game instance.
--   Construct using the `toTurnID` or `turn` functions.
data TurnID : Nat -> Type where
  MkTurnID : Fin n -> TurnID n

-- | Construct a `TurnID` from an integer from n to 1, where n is the
--   number of turns taken so far in this game instance.
toTurnID : Integer -> Maybe (TurnID n)
toTurnID {n} i = map MkTurnID (integerToFin (cast n - i) n)

-- | Construct a `TurnID` from an integer that is statically ensured to be
--   within range.
turn : (i : Integer) -> {default ItIsJust p : IsJust (toTurnID {n} i)} -> TurnID n
turn {n} i {p} with (toTurnID {n} i)
  turn {n} i {p = ItIsJust} | Just x = x

instance Eq (TurnID n) where
  (MkTurnID f) == (MkTurnID f') = f == f'
instance Show (TurnID n) where
  show (MkTurnID f) = "Turn " ++ show (cast n - finToInteger f)
instance Cast (TurnID n) (Fin n) where
  cast (MkTurnID f) = f


--
-- * ByTurn vectors
--

-- | A vector where each element corresponds to a turn in a game instance.
--   A `ByTurn` list of length n is indexed from n down to 1.
ByTurn : Nat -> Type -> Type
ByTurn = VectBy TurnID


--
-- * Static unit tests
--

test_toTurnID :
  so (toTurnID {n=3} (-1) == Nothing
   && toTurnID {n=3} 0    == Nothing
   && toTurnID {n=0} 1    == Nothing
   && toTurnID {n=1} 1    == Just (MkTurnID 0)
   && toTurnID {n=2} 1    == Just (MkTurnID 1)
   && toTurnID {n=3} 1    == Just (MkTurnID 2)
   && toTurnID {n=2} 2    == Just (MkTurnID 0)
   && toTurnID {n=3} 2    == Just (MkTurnID 1)
   && toTurnID {n=3} 3    == Just (MkTurnID 0)
   && toTurnID {n=3} 4    == Nothing)
test_toTurnID = oh

test_turn :
  so (turn {n=1} 1 == MkTurnID 0
   && turn {n=2} 1 == MkTurnID 1
   && turn {n=3} 1 == MkTurnID 2
   && turn {n=2} 2 == MkTurnID 0
   && turn {n=3} 2 == MkTurnID 1
   && turn {n=3} 3 == MkTurnID 0)
test_turn = oh

test_forTurn :
  so (for (turn 1) [7,8,9] == 9
   && for (turn 2) [7,8,9] == 8
   && for (turn 3) [7,8,9] == 7)
test_forTurn = oh
