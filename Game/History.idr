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
MoveSummary : MoveTypes np -> Type
MoveSummary = HVectBy PlayerID . map (ByTurn Z) . toVect

-- | An empty move summary.
emptyMoveSummary : {np : Nat} -> {mvs : MoveTypes np} -> MoveSummary mvs
emptyMoveSummary {np} {mvs} =
    fromHVect (initialize (\_ => fromVect {X = TurnID} Nil) (toVect mvs))
  where 
    initialize : ((t : Type) -> m t) -> (ts : Vect k Type) -> HVect (map m ts)
    initialize f (t :: ts) = f t :: initialize f ts
    initialize _ Nil       = Nil
