module Game.History

import Game.ByGame
import Game.ByTurn
import Game.ByPlayer
import Game.Tree

%default total


--
-- * Transcript
--

-- | A transcript of all move events in a single game execution.
data Transcript : (mvs : MoveTypes np) -> Type where
  Event : (i : PlayerID np) -> for i mvs -> Transcript mvs -> Transcript mvs
  End   : Transcript {np} mvs

-- | A summary of the moves played in a single game instance.
--   A ByPlayer h-vector of ByTurn vectors of moves.
MoveSummary : Vect np Nat -> MoveTypes np -> Type
MoveSummary turns = HVectBy PlayerID . zipWith ByTurn turns . toVect

  {-
using (np : Nat, mvs : MoveTypes np)

  -- | An empty move summary.
  emptyMoveSummary : MoveSummary (replicate _ Z) mvs
  emptyMoveSummary {np} {mvs} =
      fromHVect (initialize (\_ => fromVect {X = TurnID} Nil) (toVect mvs))
    where 
      initialize : ((t : Type) -> m t) -> (ts : Vect k Type) -> HVect (map m ts)
      initialize f (t :: ts) = f t :: initialize f ts
      initialize _ Nil       = Nil
  
  -- | Produce a move summary from a transcript.
  moveSummary : Transcript mvs -> MoveSummary mvs
  moveSummary = process emptyMoveSummary
    where
      process : MoveSummary mvs -> Transcript mvs -> MoveSummary mvs
      process s (Event i m t) = process (updateFor i (addTurn m) s) t
      process s End           = s
  -}
