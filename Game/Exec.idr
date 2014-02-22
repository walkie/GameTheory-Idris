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
  execMove : Transcript mvs
          -> (i : PlayerID np)
          -> for i mvs
          -> GameTree e s mvs
          -> StepResult e s mvs
  execMove t i m g = Moved (MkCurrent g (Event i m t))

  -- | Process one node in the game tree.
  step : Edge e =>
         Players m es mvs
      -> Current e s mvs
      -> {es} Eff m (StepResult e s mvs)
  step ps (MkCurrent (Leaf s p)    t) = value (Ended (MkComplete t (summarize t) p))
  step ps (MkCurrent (Node s i es) t) = do
      m <- runStrategy i ps refl
      value (maybe Failed (execMove t i m) (followEdge' es m))
