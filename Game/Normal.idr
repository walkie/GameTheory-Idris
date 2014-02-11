-- | Various representations of normal form games, smart contructors for
--   creating them, and functions for analyzing them.
--
--   TODO Generalize to n-ary normal form games?
module Game.Normal

import Data.Matrix
import Game.Class
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
fromNormal : (Eq m1, Eq m2) => Normal n1 n2 m1 m2 -> GameTree Discrete () [m1,m2]
fromNormal (MkNormal ms1 ms2 vs) =
  Node () (player 1) (DiscreteEdges (toList' (zipWith (\r,m1 => (m1,
    Node () (player 2) (DiscreteEdges (toList' (zipWith (\c,m2 => (m2,
      Leaf () (index r c vs)
    )) range ms2)))
  )) range ms1)))

-- | Convert a normal form game into a simultaneous move game.
toSimult : (Eq m1, Eq m2) => Normal n1 n2 m1 m2 -> Simult [m1,m2]
toSimult n = MkSimult (\p => lookupPayoff p n)

instance (Eq m1, Eq m2) => Game (Normal n1 n2 m1 m2) where
  numPlayers _ = 2
  edgeType   _ = Discrete
  stateType  _ = ()
  moveTypes  _ = [m1,m2]
  toGameTree   = fromNormal


--
-- * Smart Constructors
--

-- | Type of symmetric normal form games.
Symmetric : Nat -> Type -> Type
Symmetric n m = Normal n n m m

-- | Construct a two-player symmetric game.
symmetric : Vect n m -> Matrix n n Float -> Symmetric n m
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
square : Vect n m -> Matrix n n Float -> Symmetric n m
square ms vs = MkNormal ms ms (zerosum vs)


--
-- * Equilibrium solutions
--

-- | A list of all pure strategy profiles.
allProfiles : Normal n1 n2 m1 m2 -> List (Profile [m1,m2])
allProfiles {m1} {m2} (MkNormal ms1 ms2 _) =
  allProfiles {mvs = fromVect [m1,m2]} (fromHVectOf [toList ms1, toList ms2])


-- ** Nash equilbria
--

-- | Is the given solution stable? True if neither player will benefit by
--   unilaterally changing their move.
stable : (Eq m1, Eq m2) => Normal n1 n2 m1 m2 -> Profile [m1,m2] -> Bool
stable n (MkHVectBy [m1,m2]) with (moveIndexP1 m1 n, moveIndexP2 m2 n)
  | (Just r, Just c) = let vs = payoffMatrix n in
                       let v  = index r c vs   in
                          all (on (>=) (VectBy.for (player 1)) v) (col c vs)
                       && all (on (>=) (VectBy.for (player 2)) v) (row r vs)
  | _ = False -- bad input

-- | All pure Nash equilibrium solutions.
nash : (Eq m1, Eq m2) => Normal n1 n2 m1 m2 -> List (Profile [m1,m2])
nash n = filter (stable n) (allProfiles n)


-- ** Pareto efficiency
--

-- | Is the second solution a Pareto improvement on the first? True if at
--   least one player's payoff is larger and the other's is not smaller.
improve : (Eq m1, Eq m2) =>
          Normal n1 n2 m1 m2 -> Profile [m1,m2] -> Profile [m1,m2] -> Bool
improve n s s' with (lookupPayoff s n, lookupPayoff s' n)
  | (Just (MkVectBy [v1,v2]), Just (MkVectBy [v1',v2'])) =
      (v1' > v1 && v2' >= v2) || (v1' >= v1 && v2' > v2)
  | _ = False -- bad input

-- | Is the given solution Pareto optimal? True if the only way to increase
--   one player's payoff is by decreasing another's.
optimal : (Eq m1, Eq m2) => Normal n1 n2 m1 m2 -> Profile [m1,m2] -> Bool
optimal n s = all (not . improve n s) (allProfiles n)
        
-- | All strong Pareto optimal solutions.
pareto : (Eq m1, Eq m2) => Normal n1 n2 m1 m2 -> List (Profile [m1,m2])
pareto n = filter (optimal n) (allProfiles n)


--
-- * Static unit tests
--

namespace Test

  -- | Prisoner's dilemma.
  t_pd : Symmetric 2 Char
  t_pd = symmetric ['C','D'] [[2,0],[3,1]]

  -- | Stag hunt.
  t_sh : Symmetric 2 Char
  t_sh = symmetric ['C','D'] [[2,0],[1,1]]

  test_nash :
    so (nash t_pd == [profile ['D','D']]
     && nash t_sh == [profile ['C','C'], profile ['D','D']])
  test_nash = oh

  test_pareto :
    so (pareto t_pd == [profile ['C','C'], profile ['C','D'], profile ['D','C']]
     && pareto t_sh == [profile ['C','C']])
  test_pareto = oh
