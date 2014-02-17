-- | Lists where each element corresponds to a turn in a game iteration.
module Game.ByTurn

import Data.VectBy

%default total


--
-- * Turn IDs
--

-- | Identifies a turn within a game iteration.
--   Construct using the `toTurnID` or `turn` functions.
data TurnID : Type where
  MkTurnID : Nat -> TurnID

-- | Construct a `TurnID` from an integer from n to 1, where n is the
--   number of turns taken so far in this game iteration.
toTurnID : Integer -> Maybe TurnID
toTurnID i = if i > 0 then Just (MkTurnID (fromInteger i)) else Nothing

-- | Construct a `TurnID` from an integer that is statically ensured to be
--   within range.
turn : (i : Integer) -> {default ItIsJust p : IsJust (toTurnID i)} -> TurnID
turn i {p} with (toTurnID i)
  turn i {p = ItIsJust} | Just x = x

instance Eq TurnID where
  (MkTurnID n) == (MkTurnID n') = n == n'
instance Show TurnID where
  show (MkTurnID n) = "Turn " ++ show n


--
-- * ByTurn lists
--

-- | A list where each element corresponds to a turn in a game iteration.
--   A `ByTurn` list of length n is indexed from n down to 1.
data ByTurn : Type -> Type where
  MkByTurn : (n : Nat) -> Vect n a -> ByTurn a

-- | Convert a plain vector into a `ByTurn` list.
implicit
fromVect : Vect n a -> ByTurn a
fromVect {n} v = MkByTurn n v

-- | Convert a plain list into a `ByTurn` list.
fromList : List a -> ByTurn a
fromList as = MkByTurn (length as) (fromList as)

-- | The length of a `ByTurn` list.
length : ByTurn a -> Nat
length (MkByTurn l _) = l

-- | Is the given turn ID valid for this ByTurn list.
isValid : TurnID -> ByTurn a -> Bool
isValid (MkTurnID n) (MkByTurn l _) = n > 0 && n < l

for' : TurnID -> ByTurn a -> Maybe a
for' (MkTurnID n) (MkByTurn l v) =
  if n <= l then map (\f => index f v) (natToFin (l-n) l) else Nothing

-- | Index into a `ByTurn` list.
for : (i : TurnID) -> (l : ByTurn a)
   -> {default ItIsJust p : IsJust (for' i l)}
   -> a
for i l {p} with (for' i l)
  for i l {p = ItIsJust} | Just x = x

-- | Add an element corresponding to a new turn.
addTurn : a -> ByTurn a -> ByTurn a
addTurn a (MkByTurn l as) = MkByTurn (S l) (a :: as)


--
-- * Static unit tests
--

test_toTurnID :
  so (toTurnID (-1) == Nothing
   && toTurnID 0    == Nothing
   && toTurnID 1    == Just (MkTurnID 1)
   && toTurnID 2    == Just (MkTurnID 2)
   && toTurnID 3    == Just (MkTurnID 3))
test_toTurnID = oh

test_turn :
  so (turn 1 == MkTurnID 1
   && turn 2 == MkTurnID 2
   && turn 3 == MkTurnID 3)
test_turn = oh

test_forTurn' :
  so (for' (turn 1) [7,8,9] == Just 9
   && for' (turn 2) [7,8,9] == Just 8
   && for' (turn 3) [7,8,9] == Just 7
   && for' (turn 4) [7,8,9] == Nothing)
test_forTurn' = oh

test_forTurn :
  so (for (turn 1) [7,8,9] == 9
   && for (turn 2) [7,8,9] == 8
   && for (turn 3) [7,8,9] == 7)
test_forTurn = oh
