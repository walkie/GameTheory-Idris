module Game.Tree

import Game.Payoff
import Game.Util

%default total


--
-- * Representation
--

-- | The type of state stored at each node of the game tree.
StateType : Type
StateType = Type

-- | A 'ByPlayer' vector of types representing the moves that are available
--   to each player.
MoveTypes : Nat -> Type
MoveTypes np = ByPlayer np Type

-- | The form of edges in the game tree, either 'Discrete' or 'Continuous'.
EdgeType : Type
EdgeType = Type -> Type -> Type

-- | Discrete tree edges, captured by an association list of moves and the
--   subsequent game tree they produce.
data Discrete : EdgeType where
  DiscreteEdges : Eq mv => List (mv,t) -> Discrete mv t

instance Eq t => Eq (Discrete mv t) where
  (DiscreteEdges es) == (DiscreteEdges fs) = es == fs

-- | Continuous tree edges, captured by a function from moves to subsequent
--   game trees.
data Continuous : EdgeType where
  ContinuousEdges : (mv -> t) -> Continuous mv t

using (mvs : MoveTypes np)

  -- | A game tree consists of two kinds of nodes: Internal nodes present a
  --   choice to a single player, while leaf nodes yield a payoff for all
  --   players in the game. Every tree node also has an associated game state.
  data GameTree : EdgeType -> StateType -> MoveTypes np -> Type where
    Node : s -> (i : PlayerID np) -> e (for i mvs) (GameTree e s mvs) -> GameTree e s mvs
    Leaf : s -> Payoff np -> GameTree e s mvs


--
-- * Destructors
--

  -- | Returns 'True' if this is an internal node.
  isNode : GameTree e s mvs -> Bool
  isNode (Node _ _ _) = True
  isNode (Leaf _ _)   = False
  
  -- | Returns 'True' if this is an internal node.
  isLeaf : GameTree e s mvs -> Bool
  isLeaf (Node _ _ _) = False
  isLeaf (Leaf _ _)   = True

  -- | Get the state at the current game node.
  gameState : GameTree e s mvs -> s
  gameState (Node s _ _) = s
  gameState (Leaf s _)   = s

  -- | Get the ID for the player whose turn it is.
  whoseTurn : (g : GameTree e s mvs)
           -> {default refl p : isNode g = True}
           -> PlayerID np
  whoseTurn (Node _ i _) = i
  whoseTurn (Leaf _ _)   impossible

  -- | Get the ID for the player whose turn it is, if at an internal node.
  whoseTurn' : GameTree e s mvs -> Maybe (PlayerID np)
  whoseTurn' (Node _ i _) = Just i
  whoseTurn' (Leaf _ _)   = Nothing

  -- | Get the payoff at the end of a game.
  outcome : (g : GameTree e s mvs)
         -> {default refl p : isLeaf g = True}
         -> Payoff np
  outcome (Node _ _ _) impossible
  outcome (Leaf _ o)   = o

  -- | Get the payoff at the end of a game, if at a leaf node.
  outcome' : GameTree e s mvs -> Maybe (Payoff np)
  outcome' (Node _ _ _) = Nothing
  outcome' (Leaf _ o)   = Just o
  
  -- | Get the outbound moves from the current discrete internal node.
  movesFrom : (g : GameTree Discrete s mvs)
           -> {default refl p : isNode g = True}
           -> List (for (whoseTurn g {p}) mvs)
  movesFrom (Node _ _ (DiscreteEdges es)) = map fst es
  movesFrom (Leaf _ _)                    impossible

  -- | Get the children from the current discrete game node.
  children : GameTree Discrete s mvs -> List (GameTree Discrete s mvs)
  children (Node _ _ (DiscreteEdges es)) = map snd es
  children _ = []


--
-- * Game execution
--
  
  -- | Perform a move from the current discrete internal node,
  --   returns `Nothing` if the move is invalid.
  execMoveD' : (g : GameTree Discrete s mvs)
            -> {default refl p : isNode g = True}
            -> (m : for (whoseTurn g {p}) mvs)
            -> Maybe (GameTree Discrete s mvs)
  execMoveD' (Node _ _ (DiscreteEdges es)) m = lookup m es
  execMoveD' (Leaf _ _)                    _ impossible
  
  -- | Perform a move from the current discrete internal node.
  execMoveD : (g : GameTree Discrete s mvs)
           -> {default refl p1 : isNode g = True}
           -> (m : for (whoseTurn g {p = p1}) mvs)
           -> {default ItIsJust p2 : IsJust (execMoveD' g {p = p1} m)}
           -> GameTree Discrete s mvs
  execMoveD g {p1} m {p2} with (execMoveD' g {p = p1} m)
    execMoveD g {p1} m {p2 = ItIsJust} | Just t  = t
  execMoveD (Leaf _ _) _ impossible
  
  -- | Perform a move from the current continuous internal node.
  execMoveC : (g : GameTree Continuous s mvs)
         -> {default refl p : isNode g = True}
         -> for (whoseTurn g {p}) mvs
         -> GameTree Continuous s mvs
  execMoveC (Node _ _ (ContinuousEdges f)) = f
  execMoveC (Leaf _ _)                     impossible


--
-- * Search
--

  -- | Get the nodes of the game tree in BFS order.
  %assert_total
  bfs : GameTree Discrete s mvs -> List (GameTree Discrete s mvs)
  bfs t = bfs' [t]
    where 
      %assert_total
      bfs' : List (GameTree Discrete s mvs) -> List (GameTree Discrete s mvs)
      bfs' [] = []
      bfs' ns = ns ++ bfs' (concatMap children ns)
  
  -- | Get the nodes of the game tree in DFS order.
  %assert_total
  dfs : GameTree Discrete s mvs -> List (GameTree Discrete s mvs)
  dfs t = t :: concatMap dfs (children t)


--
-- * Static unit tests
--

namespace Test

  TestGame : Type
  TestGame = GameTree Discrete Char [Bool,Int]

  t_a : TestGame
  t_a = Leaf 'a' [1,2]
  
  t_b : TestGame
  t_b = Leaf 'b' [3,4]
  
  t_c : TestGame
  t_c = Leaf 'c' [5,6]
  
  t_d : TestGame
  t_d = Leaf 'd' [7,8]

  t_e : TestGame
  t_e = Node 'e' (player 1) (DiscreteEdges [(True,t_a),(False,t_b)])
  
  t_f : TestGame
  t_f = Node 'f' (player 1) (DiscreteEdges [(True,t_c),(False,t_d)])
  
  t_g : TestGame
  t_g = Node 'g' (player 2) (DiscreteEdges [(1,t_e),(2,t_f)])

  t_h : TestGame
  t_h = Node 'h' (player 2) (DiscreteEdges [(3,t_g),(4,t_e)])

  gameStates : List TestGame -> String
  gameStates = pack . map gameState

  sameStates : List TestGame -> List TestGame -> Bool
  sameStates = (==) `on` map gameState

  test_gameState :
    so (gameStates [t_a,t_b,t_c,t_d,t_e,t_f,t_g,t_h] == "abcdefgh")
  test_gameState = oh

  test_whoseTurn :
    so (whoseTurn t_e == player 1
     && whoseTurn t_f == player 1
     && whoseTurn t_g == player 2
     && whoseTurn t_h == player 2)
  test_whoseTurn = oh

  test_outcome :
    so (outcome t_a == [1,2]
     && outcome t_b == [3,4]
     && outcome t_c == [5,6]
     && outcome t_d == [7,8])
  test_outcome = oh

  test_movesFrom :
    so (movesFrom t_e == [True,False]
     && movesFrom t_f == [True,False]
     && movesFrom t_g == [1,2]
     && movesFrom t_h == [3,4])
  test_movesFrom = oh

  {- This takes several minutes to type check...
  test_children :
    so (all (isNil . children) [a,b,c,d]
     && sameStates (children e) [a,b])
     && sameStates (children f) [c,d]
     && sameStates (children g) [e,f]
     && sameStates (children h) [g,e])
  test_children = oh
  -}
  
  -- TODO for some reason, using gameStates in the following functions causes
  --      really slow type checking
  test_bfs :
    so (pack (map gameState (bfs t_h)) == "hgeefababcd")
  test_bfs = oh

  test_dfs :
    so (pack (map gameState (dfs t_h)) == "hgeabfcdeab")
  test_dfs = oh
