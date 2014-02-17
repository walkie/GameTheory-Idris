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
Summary : MoveTypes np -> Type
Summary = HVectTBy PlayerID ByTurn . toVect

using (mvs : MoveTypes np)

  -- | An empty move summary.
  emptySummary : Summary mvs
  emptySummary {mvs} = fromHVectT (initialize (\_ => Nil) (toVect mvs))
  
  -- | Add a move to a move summary.
  addMove : (i : PlayerID np) -> for i mvs -> Summary mvs -> Summary mvs
  addMove i m s ?= updateFor i (addTurn m) s
  
  -- | Produce a move summary from a transcript.
  summarize : Transcript mvs -> Summary mvs
  summarize = process emptySummary
    where
      process : Summary mvs -> Transcript mvs -> Summary mvs
      process s End           = s
      process s (Event i m t) = process (addMove i m s) t


--
-- Proofs
--
  
-- TODO Idris needs this silly proof... hopefully can remove in the future
addMove_lemma_1 = proof { intros; trivial; }
