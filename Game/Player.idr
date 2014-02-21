module Game.Player

import Effects


--
-- * Player
--

data Player : (Type -> Type) -> List EFFECT -> Type -> Type where
  MkPlayer : (name : String)
          -> (strategy : {es} Eff m mv)
          -> Player m es mv

name : Player m es mv -> String
name (MkPlayer n _) = n

strategy : Player m es mv -> {es} Eff m mv
strategy (MkPlayer _ s) = s
