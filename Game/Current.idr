module Game.ExecState

import Effects
import Effect.State

import Game.ByTurn
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

  -- | Get the current location in the game tree.
  location : Current e s mvs -> GameTree e s mvs
  location (MkCurrent l _) = l
  
  -- | Get the transcript of the current game iteration so far.
  transcript : Current e s mvs -> Transcript mvs
  transcript (MkCurrent _ t) = t

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
-- * State getters
--

  -- | Apply a function to the state of the current iteration, returning
  --   the result.
  getFromCurrent : (Current e s mvs -> a) -> {[STATE (Current e s mvs)]} Eff m a
  getFromCurrent f = do c <- get; value (f c)

  -- | Get the current location in the game tree.
  getLocation : {[STATE (Current e s mvs)]} Eff m (GameTree e s mvs)
  getLocation = getFromCurrent location

  -- | Get the transcript of the current game iteration so far.
  getTranscript : {[STATE (Current e s mvs)]} Eff m (Transcript mvs)
  getTranscript = getFromCurrent transcript
