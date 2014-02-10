module Game.Class

import Game.Tree


-- | Any game should be convertible to a game tree.
class Game g where
  
  -- | The number of players this game requires.
  numPlayers : g -> Nat

  -- | Whether the game is discrete or continuous.
  edgeType   : g -> EdgeType

  -- | The type of the game state.
  stateType  : g -> StateType

  -- | The type of the moves for each player
  moveTypes  : (x : g) -> MoveTypes (numPlayers x)

  -- | Convert the game into a game tree.
  toGameTree : (x : g) -> GameTree (edgeType x) (stateType x) (moveTypes x)
