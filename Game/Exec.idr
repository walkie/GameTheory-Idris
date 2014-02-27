--   Functions for executing game trees.
module Game.Exec

import Effects

import Game.Current
import Game.History
import Game.Player
import Game.Tree

%default total


using (mvs : MoveTypes np)

  -- | The result of processing one node in a game tree.
  data StepResult : EdgeType -> StateType -> MoveTypes np -> Type where
    Moved  : Current e s mvs -> StepResult e s mvs
    Ended  : Complete mvs    -> StepResult e s mvs
    Failed : StepResult e s mvs

  -- | Construct the step result for a successful move.
  stepMove : Transcript mvs
          -> (i : PlayerID np)
          -> for i mvs
          -> GameTree e s mvs
          -> StepResult e s mvs
  stepMove t i m g = Moved (MkCurrent g (Event i m t))

  -- | Construct the step result for the end of the game.
  stepEnd : Transcript mvs -> Payoff np -> StepResult e s mvs
  stepEnd t p = Ended (MkComplete t (summarize t) p)

  -- | Process one node in the game tree.
  step : Edge e =>
         Players m es mvs
      -> Current e s mvs
      -> {es} Eff m (StepResult e s mvs)
  step ps (MkCurrent (Leaf s p)    t) = value (stepEnd t p)
  step ps (MkCurrent (Node s i es) t) = do
      m <- runStrategy i ps refl
      value (maybe Failed (stepMove t i m) (followEdge' es m))

  -- | Run the current game iteration to completion. Returns the record of
  --   the completed game, if successful.
  %assert_total
  finish : Edge e =>
           Players m es mvs
        -> Current e s mvs
        -> {es} Eff m (Maybe (Complete mvs))
  finish ps x = do
      r <- step ps x
      case r of
        Moved y => finish ps y
        Ended y => value (Just y)
        Failed  => value Nothing

  -- | Run the given game tree once to completion. Returns the record of
  --   the completed game, if successful.
  once : Edge e =>
         Players m es mvs
      -> GameTree e s mvs
      -> {es} Eff m (Maybe (Complete mvs))
  once ps = finish ps . newIteration

  -- | Run a game tree for the given number of iterations. Returns the history
  --   of all iterations, assuming they complete successfully.
  iterate : Edge e =>
            (k : Nat)
         -> Players m es mvs
         -> GameTree e s mvs
         -> {es} Eff m (Maybe (History k mvs))
  iterate Z     ps t = value (Just [])
  iterate (S k) ps t = do
      c <- once ps t
      h <- iterate k ps t
      value (liftA2 addComplete c h)
