module Game

import VectBy
import Payoff

%default total


--
-- * Game trees
--

-- | The form of edges in the game tree, either 'Discrete' or 'Continuous'.
EdgeType : Type
EdgeType = Type -> Type -> Type

-- | Discrete tree edges, captured by an association list of moves and the
--   subsequent game tree they produce.
data Discrete : EdgeType where
  DiscreteEdges : List (m,t) -> Discrete m t

-- | Continuous tree edges, captured by a function from moves to subsequent
--   game trees.
data Continuous : EdgeType where
  ContinuousEdges : (m -> t) -> Continuous m t

-- | The type of state stored at each node of the game tree.
StateType : Type
StateType = Type

-- | A 'ByPlayer' vector of types representing the moves that are available
--   to each player.
MoveTypes : Nat -> Type
MoveTypes n = ByPlayer n Type

using (ms : MoveTypes n)

  -- | A game tree consists of two kinds of nodes: Internal nodes present a
  --   choice to a single player, while leaf nodes yield a payoff for all
  --   players in the game. Every tree node also has an associated game state.
  data GameTree : EdgeType -> StateType -> MoveTypes n -> Type where
    Node : s -> (p : PlayerID n) -> e (for p ms) (GameTree e s ms) -> GameTree e s ms
    Leaf : s -> Payoff n -> GameTree e s ms

  -- | Get the state at the current game node.
  gameState : GameTree e s ms -> s
  gameState (Node s _ _) = s
  gameState (Leaf s _)   = s

  -- | Get the outbound moves from a list of discrete edges.
  movesFrom : Discrete (for p ms) t -> List (for p ms)
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

moves : MoveTypes 2
moves = [Integer, Bool]

ex : GameTree Discrete () [Integer, Bool]
ex = Node () (player 1) (DiscreteEdges [(1, Leaf () payoff)])
