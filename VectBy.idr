module VectBy

%default total

-- * X-indexed vectors

-- | A vector indexed by some type X.
data VectBy : (Nat -> Type) -> Nat -> Type -> Type where
  MkVectBy : {X : Nat -> Type} -> Vect n a -> VectBy X n a

using (X : Nat -> Type)

  -- | Convert a plain vector into a dimen
  implicit
  fromVect : Vect n a -> VectBy X n a
  fromVect = MkVectBy

  toVect : VectBy X n a -> Vect n a
  toVect (MkVectBy v) = v

  for : Cast (X n) (Fin n) => X n -> VectBy X n a -> a
  for x (MkVectBy v) = index (cast x) v


-- ** ByPlayer vectors

-- | Identifies a player within an execution.
--   Construct using the `toPlayerID` or `player` functions.
data PlayerID : Nat -> Type where
  MkPlayerID : Fin n -> PlayerID n

-- | Construct a `PlayerID` from an integer from 1 to n, where n is the
--   number of players in this execution.
toPlayerID : Integer -> Maybe (PlayerID n)
toPlayerID {n} i = map MkPlayerID (integerToFin (i-1) n)

-- | Construct a `PlayerID` from an integer that is statically ensured to be
--   within range.
player : (i : Integer) -> {default (ItIsJust _ _) p : IsJust (toPlayerID {n} i)} -> PlayerID n
player {n} i {p} with (toPlayerID {n} i)
  player {n} i {p = ItIsJust} | Just x = x

-- | A vector where each element corresponds to a player.
--   A `ByPlayer` vector of length n is indexed from 1 up to n.
ByPlayer : Nat -> Type -> Type
ByPlayer = VectBy PlayerID

instance Eq (PlayerID n) where
  (MkPlayerID f) == (MkPlayerID f') = f == f'
instance Show (PlayerID n) where
  show (MkPlayerID f) = "Player " ++ show (cast f + 1)
instance Cast (PlayerID n) (Fin n) where
  cast (MkPlayerID f) = f


-- ** ByGame vectors

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
game : (i : Integer) -> {default (ItIsJust _ _) p : IsJust (toGameID {n} i)} -> GameID n
game {n} i {p} with (toGameID {n} i)
  game {n} i {p = ItIsJust} | Just x = x

-- | A vector where each element corresponds to a game instance.
--   A `ByGame` vector of length n is indexed from n down to 1.
ByGame : Nat -> Type -> Type
ByGame = VectBy GameID

instance Eq (GameID n) where
  (MkGameID f) == (MkGameID f') = f == f'
instance Show (GameID n) where
  show (MkGameID f) = "Game " ++ show (cast n - finToInt f 0)
instance Cast (GameID n) (Fin n) where
  cast (MkGameID f) = f


-- ** ByTurn vectors

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
turn : (i : Integer) -> {default (ItIsJust _ _) p : IsJust (toTurnID {n} i)} -> TurnID n
turn {n} i {p} with (toTurnID {n} i)
  turn {n} i {p = ItIsJust} | Just x = x

-- | A vector where each element corresponds to a turn in a game instance.
--   A `ByTurn` list of length n is indexed from n down to 1.
ByTurn : Nat -> Type -> Type
ByTurn = VectBy TurnID

instance Eq (TurnID n) where
  (MkTurnID f) == (MkTurnID f') = f == f'
instance Show (TurnID n) where
  show (MkTurnID f) = "Turn " ++ show (cast n - finToInt f 0)
instance Cast (TurnID n) (Fin n) where
  cast (MkTurnID f) = f


-- * Unit tests

test_toPlayerID :
    so (toPlayerID {n=3} (-1) == Nothing
     && toPlayerID {n=3} 0    == Nothing
     && toPlayerID {n=0} 1    == Nothing
     && toPlayerID {n=1} 1    == Just (MkPlayerID 0)
     && toPlayerID {n=2} 1    == Just (MkPlayerID 0)
     && toPlayerID {n=2} 2    == Just (MkPlayerID 1)
     && toPlayerID {n=3} 2    == Just (MkPlayerID 1)
     && toPlayerID {n=3} 3    == Just (MkPlayerID 2)
     && toPlayerID {n=3} 4    == Nothing)
test_toPlayerID = oh

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

test_player :
    so (player {n=1} 1 == MkPlayerID 0
     && player {n=2} 1 == MkPlayerID 0
     && player {n=2} 2 == MkPlayerID 1)
test_player = oh

test_game :
    so (game {n=1} 1 == MkGameID 0
     && game {n=2} 1 == MkGameID 1
     && game {n=3} 1 == MkGameID 2
     && game {n=2} 2 == MkGameID 0
     && game {n=3} 2 == MkGameID 1
     && game {n=3} 3 == MkGameID 0)
test_game = oh

test_turn :
    so (turn {n=1} 1 == MkTurnID 0
     && turn {n=2} 1 == MkTurnID 1
     && turn {n=3} 1 == MkTurnID 2
     && turn {n=2} 2 == MkTurnID 0
     && turn {n=3} 2 == MkTurnID 1
     && turn {n=3} 3 == MkTurnID 0)
test_turn = oh

test_forPlayer :
    so (for (player 1) [7,8,9] == 7
     && for (player 2) [7,8,9] == 8
     && for (player 3) [7,8,9] == 9)
test_forPlayer = oh

test_forGame :
    so (for (game 1) [7,8,9] == 9
     && for (game 2) [7,8,9] == 8
     && for (game 3) [7,8,9] == 7)
test_forGame = oh

test_forTurn :
    so (for (turn 1) [7,8,9] == 9
     && for (turn 2) [7,8,9] == 8
     && for (turn 3) [7,8,9] == 7)
test_forTurn = oh
