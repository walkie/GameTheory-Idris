module Game

import Payoff

%default total

Edges : Nat -> Type
Edges n = Fin n -> Type -> Vect n Type -> Type

Moves : Nat -> Type
Moves n = Vect n Type

using (e : Edges n, ms : Moves n)

  data GameTree : Edges n -> Type -> Moves n -> Type where
    Node : s -> (p : Fin n) -> e p s ms -> GameTree e s ms
    Leaf : s -> Payoff n                -> GameTree e s ms

  data Discrete : Edges n where
    DiscreteEdges : List (index p ms, GameTree Discrete s ms) -> Discrete p s ms
  
  data Continuous : Edges n where
    ContinuousEdges : (index p ms -> GameTree Continuous s ms) -> Continuous p s ms

  -- | Get the state at the current game node.
  gameState : GameTree e s ms -> s
  gameState (Node s _ _) = s
  gameState (Leaf s _)   = s

  -- | Get the game outbound moves from a list of discrete edges.
  movesFrom : Discrete p s ms -> List (index p ms)
  movesFrom (DiscreteEdges es) = map fst es
  
  -- | Get the children from the current game node.
  children : GameTree Discrete s ms -> List (GameTree Discrete s ms)
  children (Node _ _ (DiscreteEdges es)) = map snd es
  children _ = []

  -- | Get the nodes of the game tree in BFS order.
  %assert_total
  bfs : GameTree Discrete s ms -> List (GameTree Discrete s ms)
  bfs t = bfs' [t]
    where 
      %assert_total
      bfs' : List (GameTree Discrete s ms) -> List (GameTree Discrete s ms)
      bfs' [] = []
      bfs' ns = ns ++ bfs' (concatMap children ns)
  
  -- | Get the nodes of the game tree in DFS order.
  %assert_total
  dfs : GameTree Discrete s ms -> List (GameTree Discrete s ms)
  dfs t = t :: concatMap dfs (children t)


-- Examples

payoff : Payoff 2
payoff = [2.0, -1.0]

moves : Moves 2
moves = [Integer, Bool]

ex : GameTree Discrete () [Integer, Bool]
ex = Node () 0 (DiscreteEdges [(1, Leaf () payoff)])
