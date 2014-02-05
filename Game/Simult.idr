-- | Simultaneous move games. This representation supports continuous domains
--   of moves. For discrete domains, see 'Game.Normal'.
module Game.Simult

import Game.ByPlayer
import Game.Payoff
import Game.Tree


-- | Pure strategy profile; one move per player.
Profile : MoveTypes n -> Type
Profile = ByPlayer'
  
-- | A general simultaneous move game. Maps a strategy profile to a payoff.
data Simult : MoveTypes n -> Type where
  MkSimult : {ms : MoveTypes n} -> (Profile ms -> Payoff n) -> Simult ms

-- | Get the payoff function for a simultaneous game.
payoffFun : {ms : MoveTypes n} -> Simult ms -> Profile ms -> Payoff n
payoffFun (MkSimult f) = f

-- | Captures games that can be converted into a simultaneous move game.
class IsSimult (g : MoveTypes n -> Type) where
  toSimult : g ms -> Simult ms

instance IsSimult (Simult {n}) where
  toSimult = id
