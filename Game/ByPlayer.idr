-- | Vectors where each element corresponds to a particular player.
module Game.ByPlayer

import Data.HVectBy
import Data.HVectListBy
import Data.VectBy

%default total


--
-- * Player IDs
--

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
player : (i : Integer) -> {default ItIsJust p : IsJust (toPlayerID {n} i)} -> PlayerID n
player {n} i {p} with (toPlayerID {n} i)
  player {n} i {p = ItIsJust} | Just x = x

instance Eq (PlayerID n) where
  (MkPlayerID f) == (MkPlayerID f') = f == f'
instance Show (PlayerID n) where
  show (MkPlayerID f) = "Player " ++ show (cast f + 1)
instance Cast (PlayerID n) (Fin n) where
  cast (MkPlayerID f) = f


--
-- * ByPlayer vectors
--

-- | A vector where each element corresponds to a player.
--   A `ByPlayer` vector of length n is indexed from 1 up to n.
ByPlayer : Nat -> Type -> Type
ByPlayer = VectBy PlayerID

-- | An h-vector where each element corresponds to a player.
--   Indexed from 1 to n.
--   TODO Better name?
ByPlayerH : ByPlayer n Type -> Type
ByPlayerH = HVectBy PlayerID . toVect

-- | An h-vector of lists where each list corresponds to a player.
--   Indexed from 1 to n.
--   TODO Better name?
ByPlayerHL : ByPlayer n Type -> Type
ByPlayerHL = HVectListBy PlayerID . toVect


--
-- * Static unit tests
--

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

test_player :
  so (player {n=1} 1 == MkPlayerID 0
   && player {n=2} 1 == MkPlayerID 0
   && player {n=2} 2 == MkPlayerID 1)
test_player = oh

test_forPlayer :
  so (for (player 1) [7,8,9] == 7
   && for (player 2) [7,8,9] == 8
   && for (player 3) [7,8,9] == 9)
test_forPlayer = oh
