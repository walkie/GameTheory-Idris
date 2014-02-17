-- | Functions for executing game trees.
module Game.Exec

import Game.Class
import Game.History
import Game.Tree

%default total


-- | The state of a game iteration execution.
-- 
--   TODO I'd like to define a record here to auto-generate
--        getters and setters, but this bug breaks it:
--        https://github.com/idris-lang/Idris-dev/issues/262
data Exec : EdgeType -> StateType -> MoveTypes np -> Type where
  MkExec : (location   : GameTree {np} e s mvs)
        -> (transcript : Transcript mvs)
        -> Exec e s mvs

using (mvs : MoveTypes np)

  -- | The initial game execution state.
  initExec : GameTree e s mvs -> Exec e s mvs
  initExec l = MkExec l End
  
  -- | Set the current location.
  setLocation : GameTree e s mvs -> Exec e s mvs -> Exec e s mvs
  setLocation l (MkExec _ t) = MkExec l t

  -- | Add an event to the transcript.
  addEvent : (i : PlayerID np) -> for i mvs -> Exec e s mvs -> Exec e s mvs
  addEvent i m (MkExec l t) = MkExec l (Event i m t)
