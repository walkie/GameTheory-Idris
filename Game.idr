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
    Node : s -> (i : PlayerID n) -> e (for i ms) (GameTree e s ms) -> GameTree e s ms
    Leaf : s -> Payoff n -> GameTree e s ms

  -- | Returns 'True' if this is an internal node.
  isNode : GameTree e s ms -> Bool
  isNode (Node _ _ _) = True
  isNode (Leaf _ _)   = False
  
  -- | Returns 'True' if this is an internal node.
  isLeaf : GameTree e s ms -> Bool
  isLeaf (Node _ _ _) = False
  isLeaf (Leaf _ _)   = True

  -- | Get the state at the current game node.
  gameState : GameTree e s ms -> s
  gameState (Node s _ _) = s
  gameState (Leaf s _)   = s

  -- | Get the ID for the player whose turn it is.
  whoseTurn : (g : GameTree e s ms)
           -> {default refl p : isNode g = True}
           -> PlayerID n
  whoseTurn (Node _ i _) = i
  whoseTurn (Leaf _ _)   impossible

  -- | Get the ID for the player whose turn it is, if at an internal node.
  whoseTurn' : GameTree e s ms -> Maybe (PlayerID n)
  whoseTurn' (Node _ i _) = Just i
  whoseTurn' (Leaf _ _)   = Nothing

  -- | Get the payoff at the end of a game.
  outcome : (g : GameTree e s ms)
         -> {default refl p : isLeaf g = True}
         -> Payoff n
  outcome (Node _ _ _) impossible
  outcome (Leaf _ o)   = o

  -- | Get the payoff at the end of a game, if at a leaf node.
  outcome' : GameTree e s ms -> Maybe (Payoff n)
  outcome' (Node _ _ _) = Nothing
  outcome' (Leaf _ o)   = Just o
  
  -- | Get the outbound moves from a list of discrete edges.
  moves : Discrete m t -> List m
  moves (DiscreteEdges es) = map fst es

  -- | Get the outbound moves from the current internal node.
  --   TODO: Figure out how to avoid 'really_believe_me' below. Must prove
  --         that 'whoseTurn' returns the same i stored in the 'Node'.
  movesFrom : (g : GameTree Discrete s ms)
           -> {default refl p1 : isNode g = True}
           -> {default refl p2 : whoseTurn g {p = p1} = i}
           -> List (for i ms)
  movesFrom (Node _ i' e) = really_believe_me (moves e)
  movesFrom (Leaf _ _)    impossible

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


--
-- * Static unit tests
--
  
namespace Test

  TestGame : Type
  TestGame = GameTree Discrete Char [Bool,Int]

  a : TestGame
  a = Leaf 'a' [1,2]
  
  b : TestGame
  b = Leaf 'b' [3,4]
  
  c : TestGame
  c = Leaf 'c' [5,6]
  
  d : TestGame
  d = Leaf 'd' [7,8]

  e : TestGame
  e = Node 'e' (player 1) (DiscreteEdges [(True,a),(False,b)])
  
  f : TestGame
  f = Node 'f' (player 1) (DiscreteEdges [(True,c),(False,d)])
  
  g : TestGame
  g = Node 'g' (player 2) (DiscreteEdges [(1,e),(2,f)])

  h : TestGame
  h = Node 'h' (player 2) (DiscreteEdges [(3,g),(4,e)])

  test_gameState :
    so (pack (map gameState [a,b,c,d,e,f,g,h]) == "abcdefgh")
  test_gameState = oh

  test_whoseTurn :
    so (whoseTurn e == player 1
     && whoseTurn f == player 1
     && whoseTurn g == player 2
     && whoseTurn h == player 2)
  test_whoseTurn = oh

  test_outcome :
    so (outcome a == [1,2]
     && outcome b == [3,4]
     && outcome c == [5,6]
     && outcome d == [7,8])
  test_outcome = oh

  test_movesFrom :
    so (movesFrom e == [True,False]
     && movesFrom f == [True,False]
     && movesFrom g == [1,2]
     && movesFrom h == [3,4])
  test_movesFrom = oh
