-- | Simultaneous move games. This representation supports continuous domains
--   of moves. For discrete domains, see 'Game.Normal'.
module Game.Simult

import Game.Payoff
import Game.Profile
import Game.Tree

%default total


-- | A general simultaneous move game. Maps a strategy profile to a payoff.
data Simult : MoveTypes np -> Type where
  MkSimult : {mvs : MoveTypes np} -> (Profile mvs -> Payoff np) -> Simult mvs

-- | Get the payoff function for a simultaneous game.
payoffFun : {mvs : MoveTypes np} -> Simult mvs -> Profile mvs -> Payoff np
payoffFun (MkSimult f) = f

-- | Captures games that can be converted into a simultaneous move game.
class IsSimult (g : MoveTypes np -> Type) where
  toSimult : g mvs -> Simult mvs

instance IsSimult (Simult {np}) where
  toSimult = id
