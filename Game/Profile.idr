-- | A simple representation of pure strategy profiles.
module Game.Profile

import Game.ByPlayer


-- | Pure strategy profile; one move per player.
Profile : MoveTypes np -> Type
Profile = ByPlayerH
