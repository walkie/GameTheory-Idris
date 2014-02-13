module Game.Tree

import Game.Move
import Game.Payoff

%default total


--
-- * Representation
--

-- | The type of state stored at each node of the game tree.
StateType : Type
StateType = Type

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
  ContinuousEdges : (mv -> Maybe t) -> Continuous mv t

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

  -- | Perform a move from the current continuous internal node,
  --   returns `Nothing` if the move is invalid.
  execMoveC' : (g : GameTree Continuous s mvs)
            -> {default refl p : isNode g = True}
            -> (m : for (whoseTurn g {p}) mvs)
            -> Maybe (GameTree Continuous s mvs)
  execMoveC' (Node _ _ (ContinuousEdges f)) m = f m
  execMoveC' (Leaf _ _)                     _ impossible
  
  -- | Perform a move from the current continuous internal node.
  execMoveC : (g : GameTree Continuous s mvs)
           -> {default refl p1 : isNode g = True}
           -> (m : for (whoseTurn g {p = p1}) mvs)
           -> {default ItIsJust p2 : IsJust (execMoveC' g {p = p1} m)}
           -> GameTree Continuous s mvs
  execMoveC g {p1} m {p2} with (execMoveC' g {p = p1} m)
    execMoveC g {p1} m {p2 = ItIsJust} | Just t  = t
  execMoveC (Leaf _ _) _ impossible


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
