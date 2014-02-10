module Game.TreeTest

import Game.Tree
import Game.Util

%default total


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
