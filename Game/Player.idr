module Game.Player

import Effects

import Game.ByPlayer
import Game.Move


--
-- * Player
--

-- | A player has a name and a strategy.
data Player : (Type -> Type) -> List EFFECT -> Type -> Type where
  MkPlayer : (name : String)
          -> (strategy : {es} Eff m mv)
          -> Player m es mv

-- | The player's name.
name : Player m es mv -> String
name (MkPlayer n _) = n

moveType : Player m es mv -> Type
moveType {mv} _ = mv

-- | The player's strategy. A potentially effectful computation that yields
--   a move.
strategy : Player m es mv -> {es} Eff m mv
strategy (MkPlayer _ s) = s

-- | A `ByPlayer` vector of players.
Players : (Type -> Type) -> List EFFECT -> MoveTypes np -> Type
Players m es mvs = HVectTBy PlayerID (Player m es) (toVect mvs)
-- Players : (Type -> Type) -> ByPlayer np (List EFFECT) -> MoveTypes np -> Type
-- Players m ess mvs = HVectBy PlayerID (zipWith (Player m) (toVect ess) (toVect mvs))

-- | Get a particular player from a `Players` vector.
player : {mvs : MoveTypes np}
      -> (i : PlayerID np)
      -> Players m es mvs
      -> (for i mvs = mv)
      -> Player m es mv
player {mvs} i ps refl = HVectTBy.for {c = Player m es} {ts = toVect mvs} i ps

-- | Run the strategy of a particular player.
runStrategy : {mvs : MoveTypes np}
           -> (i : PlayerID np)
           -> (ps : Players m es mvs)
           -> (for i mvs = mv)
           -> {es} Eff m mv
runStrategy i ps p = strategy (player i ps p)
