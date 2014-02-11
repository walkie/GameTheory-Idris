-- | A simple representation of pure strategy profiles.
module Game.Profile

import Data.HVectOf
import Game.ByPlayer
import Game.Tree

%default total


-- | Pure strategy profile; one move per player.
Profile : MoveTypes np -> Type
Profile = ByPlayerH

-- | Build a profile from a vector of moves.
profile : HVect {k} ts -> Profile {np = k} (fromVect ts)
profile = MkHVectBy

-- | A list of all pure strategy profiles.
allProfiles : {mvs : MoveTypes np} -> ByPlayerOf List mvs -> List (Profile mvs)
allProfiles = map profile . cartesianProduct . toHVectOf
