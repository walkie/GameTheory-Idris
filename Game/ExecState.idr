module Game.ExecState

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
-- * State of the current iteration
--

-- | The state of execution of the current game iteration.
-- 
--   TODO I'd like to define a record here to auto-generate
--        getters and setters, but this bug breaks it:
--        https://github.com/idris-lang/Idris-dev/issues/262
data Current : EdgeType -> StateType -> MoveTypes np -> Type where
  MkCurrent : (location   : GameTree {np} e s mvs)
           -> (transcript : Transcript mvs)
           -> Current e s mvs

using (mvs : MoveTypes np)

  -- | The initial game execution state.
  newIteration : GameTree e s mvs -> Current e s mvs
  newIteration l = MkCurrent l End
  
  -- | Set the current location.
  setLocation : GameTree e s mvs -> Current e s mvs -> Current e s mvs
  setLocation l (MkCurrent _ t) = MkCurrent l t

  -- | Add an event to the transcript.
  addEvent : (i : PlayerID np) -> for i mvs -> Current e s mvs -> Current e s mvs
  addEvent i m (MkCurrent l t) = MkCurrent l (Event i m t)


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
-- * State of completed iterations
--

-- | A record of a completed game iteration, consisting of a transcript,
--   a move summary, and the resulting payoff.
data Complete : MoveTypes np -> Type where
  MkComplete : {mvs : MoveTypes np}
             -> (transcript : Transcript mvs)
             -> (summary    : Summary mvs)
             -> (payoff     : Payoff np)
             -> Complete mvs

using (mvs : MoveTypes np)

  -- | Get the transcript from an iteration record.
  transcript : Complete mvs -> Transcript mvs
  transcript (MkComplete t _ _) = t
  
  -- | Get the move summary from an iteration record.
  summary : Complete mvs -> Summary mvs
  summary (MkComplete _ s _) = s
  
  -- | Get the payoff from an iteration record.
  payoff : Complete mvs -> Payoff np
  payoff (MkComplete _ _ p) = p


--
-- * Execution history
--

-- | The execution history of an iterated game: a transcript and summary
--   of each completed iteration.
History : Nat -> MoveTypes np -> Type
History n mvs = ByGame {n} (Complete mvs)

using (mvs : MoveTypes np)

  -- | Get the transript for each game iteration.
  transcripts : History n mvs -> ByGame {n} (Transcript mvs)
  transcripts = map transcript
  
  -- | Get the move summary for each game iteration.
  summaries : History n mvs -> ByGame {n} (Summary mvs)
  summaries = map summary
  
  -- | Get the move summary for each game iteration.
  payoffs : History n mvs -> ByGame {n} (Payoff np)
  payoffs = map payoff
  
  -- | Compute the score from a history.
  score : History n mvs -> Payoff np
  score = foldr (<+>) tie . payoffs


--
-- Proofs
--
  
-- TODO Idris needs this silly proof... hopefully can remove in the future
addMove_lemma_1 = proof { intros; trivial; }
