-- | Various representations of normal form games, smart contructors for
--   creating them, and functions for analyzing them.
--
--   TODO Generalize to n-ary normal form games?
module Game.Normal

import Data.Matrix
import Game.Payoff
import Game.Tree
import Game.Util


--
-- * Representation
--

-- | A two-player normal form game.
data Normal : Nat -> Nat -> Type -> Type -> Type where
  MkNormal : Vect n1 m1 -> Vect n2 m2 -> Matrix n1 n2 (Payoff 2) -> Normal n1 n2 m1 m2

-- | Get the moves for player 1.
movesP1 : Normal n1 n2 m1 m2 -> Vect n1 m1
movesP1 (MkNormal ms _ _) = ms

-- | Get the moves for player 2.
movesP2 : Normal n1 n2 m1 m2 -> Vect n2 m2
movesP2 (MkNormal _ ms _) = ms

-- | Get the payoff matrix for this game.
payoffMatrix : Normal n1 n2 m1 m2 -> Matrix n1 n2 (Payoff 2)
payoffMatrix (MkNormal _ _ vs) = vs

-- | Convert a normal form game into a game tree.
toGameTree : Normal n1 n2 m1 m2 -> GameTree Discrete () [m1,m2]
toGameTree (MkNormal ms1 ms2 vs) =
  Node () (player 1) (DiscreteEdges (toList' (zipWith (\r,m1 => (m1,
    Node () (player 2) (DiscreteEdges (toList' (zipWith (\c,m2 => (m2,
      Leaf () (index r c vs)
    )) range ms2)))
  )) range ms1)))


--
-- * Smart Constructors
--

-- | Construct a two-player symmetric game.
symmetric : Vect n m -> Matrix n n Float -> Normal n n m m
symmetric ms vs = MkNormal ms ms (buildMatrix pay)
  where pay r c = payoff [index r c vs, index c r vs]

-- | Construct a zero-sum payoff matrix from a matrix of floats.
zerosum : Matrix n1 n2 Float -> Matrix n1 n2 (Payoff 2)
zerosum = map (map (\v => payoff [v,-v]))

-- | Construct a two-player zero-sum game. The payoffs are given from the
--   first player's perspective.
matrix : Vect n1 m1 -> Vect n2 m2 -> Matrix n1 n2 Float -> Normal n1 n2 m1 m2
matrix ms1 ms2 vs = MkNormal ms1 ms2 (zerosum vs)

-- | Construct a two-player symmetric zero-sum game.
square : Vect n m -> Matrix n n Float -> Normal n n m m
square ms vs = MkNormal ms ms (zerosum vs)
