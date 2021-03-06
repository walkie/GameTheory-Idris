--   This module provides a higher-level way to build game trees for games
--   that are centered around the manipulation of state.
module Game.StateBased

import Game.Tree


--
-- * State-based games
--

-- ** Continuous games
--

-- | Build a continuous game tree for a state-based game.
stateTreeC :
     {s : Type} -> {np : Nat} -> {mvs : MoveTypes np}
  -> (s -> Bool)                                      -- Is the game over?
  -> (s -> PlayerID np)                               -- Whose turn is it?
  -> (s -> (i : PlayerID np) -> for i mvs -> Maybe s) -- Execute a move and return the new state.
  -> (s -> Payoff np)                                 -- Payoff for this (final) state.
  -> s                                                -- The initial state.
  -> GameTree Continuous s mvs
stateTreeC end who exec pay = tree
  where 
    tree s with (end s)
      | True  = Leaf s (pay s)
      | False = let i = who s in
                Node s i (ContinuousEdges (\m => map tree (exec s i m)))

-- | Build a continuous game tree by taking turns, making moves until some
--   condition is met.
takeTurnsC :
     {s : Type} -> {np : Nat} -> {mvs : MoveTypes (S np)}
  -> (s -> PlayerID (S np) -> Bool)                       -- Is the game over?
  -> (s -> (i : PlayerID (S np)) -> for i mvs -> Maybe s) -- Execute a move and return the new state.
  -> (s -> PlayerID (S np) -> Payoff (S np))              -- Payoff for this (final) state.
  -> s                                                    -- The initial state.
  -> PlayerID (S np)                                      -- The ID of the initial player.
  -> GameTree Continuous s mvs
takeTurnsC end exec pay = tree
  where
    tree s i with (end s i)
      | True  = Leaf s (pay s i)
      | False = Node s i (ContinuousEdges 
                (\m => map (\s => tree s (nextPlayer i)) (exec s i m)))


-- ** Discrete games
--

{- TODO need a way to say that all types in `mvs` instantiate `Eq`...

-- | Build a discrete game tree for a state-based game.
stateTreeD :
     {s : Type} -> {np : Nat} -> {mvs : MoveTypes np}
  -> (s -> Bool)                                  -- Is the game over?
  -> (s -> PlayerID np)                           -- Whose turn is it?
  -> (s -> (i : PlayerID np) -> List (for i mvs)) -- Available moves.
  -> (s -> (i : PlayerID np) -> for i mvs -> s)   -- Execute a move and return the new state.
  -> (s -> Payoff np)                             -- Payoff for this (final) state.
  -> s                                            -- The initial state.
  -> GameTree Discrete s mvs
stateTreeD end who avail exec pay = tree
  where
    tree s with (end s)
      | True  = Leaf s (pay s)
      | False = let i = who s in
                Node s i (DiscreteEdges (map
                           (\m => (m, tree (exec s i m)))
                           (avail s i)))

-- | Build a discrete game tree by taking turns, making moves until some
--   condition is met.
takeTurnsD :
     {s : Type} -> {np : Nat} -> {mvs : MoveTypes (S np)}
  -> (s -> PlayerID (S np) -> Bool)                   -- Is the game over?
  -> (s -> (i : PlayerID (S np)) -> List (for i mvs)) -- Available moves.
  -> (s -> (i : PlayerID (S np)) -> for i mvs -> s)   -- Execute a move and return the new state.
  -> (s -> PlayerID (S np) -> Payoff (S np))          -- Payoff for this (final) state.
  -> s                                                -- The initial state.
  -> PlayerID (S np)                                  -- The ID of the initial player.
  -> GameTree Discrete s mvs
takeTurnsD end avail exec pay = tree
  where
    tree s i with (end s i)
      | True  = Leaf s (pay s i)
      | False = Node s i (DiscreteEdges (map
                           (\m => (m, tree (exec s i m) (nextPlayer i)))
                           (avail s i)))
-}
