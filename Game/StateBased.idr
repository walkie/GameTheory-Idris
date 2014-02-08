-- | This module provides a higher-level way to build game trees for games
--   that are centered around the manipulation of state.
module Game.StateBased

import Game.Tree


--
-- * State-based games
--

-- | Build a discrete game tree for a state-based game.
stateTreeD :
     {s : Type} -> {np : Nat} -> {mvs : MoveTypes np}
  -> (s -> Bool)                                  -- ^ Is the game over?
  -> (s -> PlayerID np)                           -- ^ Whose turn is it?
  -> (s -> (i : PlayerID np) -> List (for i mvs)) -- ^ Available moves.
  -> (s -> (i : PlayerID np) -> for i mvs -> s)   -- ^ Execute a move and return the new state.
  -> (s -> Payoff np)                             -- ^ Payoff for this (final) state.
  -> s                                            -- ^ The initial state.
  -> GameTree Discrete s mvs
stateTreeD end who avail exec pay = tree
  where
    tree s with (end s)
      | True  = Leaf s (pay s)
      | False = let i = who s in
                Node s i (DiscreteEdges (map (\m => (m, tree (exec s i m))) (avail s i)))

-- | Build a continuous game tree for a state-based game.
stateTreeC :
     {s : Type} -> {np : Nat} -> {mvs : MoveTypes np}
  -> (s -> Bool)                                  -- ^ Is the game over?
  -> (s -> PlayerID np)                           -- ^ Whose turn is it?
  -> (s -> (i : PlayerID np) -> for i mvs -> s)   -- ^ Execute a move and return the new state.
  -> (s -> Payoff np)                             -- ^ Payoff for this (final) state.
  -> s                                            -- ^ The initial state.
  -> GameTree Continuous s mvs
stateTreeC end who exec pay = tree
  where 
    tree s with (end s)
      | True  = Leaf s (pay s)
      | False = let i = who s in
                Node s i (ContinuousEdges (\m => tree (exec s i m)))
