-- | Various representations of normal form games, smart contructors for
--   creating them, and functions for analyzing them.
--
--   TODO Generalize to n-ary normal form games?
module Game.Normal

import Data.Matrix
import Game.Payoff
import Game.Profile
import Game.Simult
import Game.Tree
import Game.Util

%default total


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


--
-- * Game resolution
--

-- | Get the index of a move for player 1.
moveIndexP1 : Eq m1 => m1 -> Normal n1 n2 m1 m2 -> Maybe (Fin n1)
moveIndexP1 {n1} m (MkNormal ms _ vs) with (elemIndex m ms)
  | Just i = natToFin i n1
  | _      = Nothing

-- | Get the index of a move for player 2.
moveIndexP2 : Eq m2 => m2 -> Normal n1 n2 m1 m2 -> Maybe (Fin n2)
moveIndexP2 {n2} m (MkNormal _ ms vs) with (elemIndex m ms)
  | Just i = natToFin i n2
  | _      = Nothing

-- | Lookup the result of strategy profile in the payoff matrix.
lookupPayoff : (Eq m1, Eq m2) => Profile [m1,m2] -> Normal n1 n2 m1 m2 -> Maybe (Payoff 2)
lookupPayoff {n1} {n2} (MkHVectBy [m1,m2]) n = do
  r <- moveIndexP1 m1 n
  c <- moveIndexP2 m2 n
  return (index r c (payoffMatrix n))


--
-- * Conversion to other game types
--

-- | Convert a normal form game into a game tree.
toGameTree : Normal n1 n2 m1 m2 -> GameTree Discrete () [m1,m2]
toGameTree (MkNormal ms1 ms2 vs) =
  Node () (player 1) (DiscreteEdges (toList' (zipWith (\r,m1 => (m1,
    Node () (player 2) (DiscreteEdges (toList' (zipWith (\c,m2 => (m2,
      Leaf () (index r c vs)
    )) range ms2)))
  )) range ms1)))

-- | Convert a normal form game into a simultaneous move game. Yields the
--   provided default payoff for any strategy profile that is not included
--   in the normal form game.
toSimult : (Eq m1, Eq m2) => Payoff 2 -> Normal n1 n2 m1 m2 -> Simult [m1,m2]
toSimult def n = MkSimult (\p => fromMaybe def (lookupPayoff p n))


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

-- | A list of all pure strategy profiles.
allProfiles : Normal n1 n2 m1 m2 -> List (Profile [m1,m2])
allProfiles {m1} {m2} (MkNormal ms1 ms2 _) =
  allProfiles {mvs = fromVect [m1,m2]} (fromHVectList [toList ms1, toList ms2])
