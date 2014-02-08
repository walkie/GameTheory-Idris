-- | A simple representation of pure strategy profiles.
module Game.Profile

import Data.HVectList
import Game.ByPlayer
import Game.Tree

%default total


-- | Pure strategy profile; one move per player.
Profile : MoveTypes np -> Type
Profile = ByPlayerH

-- | Build a profile from a vector of moves.
profile : {mvs : MoveTypes np} -> HVect (toVect mvs) -> Profile mvs
profile = MkHVectBy

-- | A list of all pure strategy profiles.
allProfiles : {mvs : MoveTypes np} -> ByPlayerHL mvs  -> List (Profile mvs)
allProfiles = map profile . cartesianProduct . toHVectList
