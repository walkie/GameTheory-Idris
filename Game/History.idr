module Game.History

import Game.ByGame
import Game.ByTurn
import Game.ByPlayer
import Game.Tree

%default total


--
-- * Transcript
--

-- | A transcript of all move events in a single game iteration.
data Transcript : (mvs : MoveTypes np) -> Type where
  Event : (i : PlayerID np) -> for i mvs -> Transcript mvs -> Transcript mvs
  End   : Transcript {np} mvs


--
-- * Move summaries
--

-- | A summary of the moves played in a single game iteration.
--   A ByPlayer h-vector of ByTurn vectors of moves.
MoveSummary : MoveTypes np -> Type
MoveSummary = HVectTBy PlayerID ByTurn . toVect

using (mvs : MoveTypes np)

  -- | An empty move summary.
  emptyMoveSummary : MoveSummary mvs
  emptyMoveSummary {mvs} = fromHVectT (initialize (\_ => Nil) (toVect mvs))
  
  -- | Add a move to a move summary.
  addMove : (i : PlayerID np) -> for i mvs -> MoveSummary mvs -> MoveSummary mvs
  addMove i m s ?= updateFor i (addTurn m) s
  
  -- | Produce a move summary from a transcript.
  moveSummary : Transcript mvs -> MoveSummary mvs
  moveSummary = process emptyMoveSummary
    where
      process : MoveSummary mvs -> Transcript mvs -> MoveSummary mvs
      process s End           = s
      process s (Event i m t) = process (addMove i m s) t


--
-- Proofs
--
  
-- TODO Idris needs this silly proof... hopefully can remove in the future
addMove_lemma_1 = proof { intros; trivial; }
