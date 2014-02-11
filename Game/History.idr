module Game.History where

import Game.ByGame
import Game.ByTurn
import Game.ByPlayer

%default total


--
-- * Transcript
--

-- | A transcript of all move events in a single game execution.
data Transcript : {np : Nat} -> (mvs : MoveTypes np) -> Type where
  Event : (i : PlayerID np) -> for i mvs -> Transcript mvs -> Transcript mvs
  End   : Transcript mvs
