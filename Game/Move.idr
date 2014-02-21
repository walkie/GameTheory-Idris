--   A simple representation of pure strategy profiles.
module Game.Move

import Data.HVectBy
import Data.HVectTBy
import Game.ByPlayer

%default total


--
-- * Moves
--

-- | A `ByPlayer` vector of types representing the moves that are available
--   to each player.
MoveTypes : Nat -> Type
MoveTypes np = ByPlayer np Type

-- | A `ByPlayer` vector of lists containing moves of the type available to
--   each player.
Moves : MoveTypes np -> Type
Moves = HVectTBy PlayerID List . toVect


--
-- * Strategy profiles
--

-- | Pure strategy profile; one move per player.
Profile : MoveTypes np -> Type
Profile = HVectBy PlayerID . toVect

-- | Build a profile from a vector of moves.
profile : HVect {k} ts -> Profile {np = k} (fromVect ts)
profile = MkHVectBy

-- | A list of all pure strategy profiles.
allProfiles : {mvs : MoveTypes np} -> Moves mvs -> List (Profile mvs)
allProfiles = map profile . cartesianProduct . toHVectT
