module Game.History

import Game.ByGame
import Game.Current

%default total


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
