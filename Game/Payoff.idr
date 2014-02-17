-- | The outcome of a game is a payoff.  This module provides a simple
--   representation of payoffs, smart constructors for building typical
--   payoffs, and functions for pretty printing them.
module Game.Payoff

import Data.Floats
import Game.ByPlayer

%default total


--
-- * Representation
--

-- | Payoffs are represented as a vector of 'Float' values where each value
--   corresponds to a particular player.
--   While the type of payoffs could be generalized, this representation
--   supports both cardinal and ordinal payoffs while being easy to work with.
Payoff : Nat -> Type
Payoff np = VectBy PlayerID np Float

-- | Create a payoff from a vector.
payoff : Vect np Float -> Payoff np
payoff = fromVect


--
-- * Smart constructors
--

-- | Payoff where all players score payoff a, except player p, who scores b.
allBut : PlayerID np -> Float -> Float -> Payoff np
allBut p a b = replaceAt (cast p) b (replicate _ a)

-- | Zero-sum payoff where player p wins (scoring np-1) 
--   and all other players lose (scoring -1).
winner : PlayerID np -> Payoff np
winner {np} p = allBut p (-1) (fromInteger (cast np) - 1)

-- | Zero-sum payoff where player p wins (scoring np-1) 
--   and all other players lose (scoring -1).
loser : PlayerID np -> Payoff np
loser {np} p = allBut p 1 (1 - fromInteger (cast np))

-- | Zero-sum payoff where all players tie. Each player scores 0.
tie : Payoff np
tie = replicate _ 0


--
-- * Group instances
--

instance Semigroup (Payoff np) where
  (<+>) (MkVectBy v) (MkVectBy w) = MkVectBy (zipWith (+) v w)

instance Monoid (Payoff np) where
  neutral = tie

instance Group (Payoff np) where
  inverse (MkVectBy v) = MkVectBy (map (0-) v)

instance AbelianGroup (Payoff np) where { }


--
-- * Pretty printing
--

-- | Pretty print floats as integers, when possible.
showFloat : Float -> String
showFloat f = if f == floor f then fst (break (== '.') s) else s
  where s = show f

-- | Show a list of strings as a comma-separated sequence.
--   TODO bug in Idris requires qualified Nil below.
showSeq : List String -> String
showSeq []        = ""
showSeq (s :: List.Nil) = s
showSeq (s :: ss) = s ++ "," ++ showSeq ss

-- | String representation of a Payoff.
showPayoff : Payoff np -> String
showPayoff = showSeq . toList . map showFloat

-- | Bracketed string representation of a Payoff.
showPayoffAsList : Payoff np -> String
showPayoffAsList p = "[" ++ showPayoff p ++ "]"


--
-- * Static unit tests
--

test_allBut :
  so (allBut (player 1) 2 3 == payoff [3]
   && allBut (player 1) 2 3 == payoff [3,2]
   && allBut (player 1) 2 3 == payoff [3,2,2]
   && allBut (player 2) 2 3 == payoff [2,3,2]
   && allBut (player 3) 2 3 == payoff [2,2,3])
test_allBut = oh

test_winner :
  so (winner (player 1) == payoff [0]
   && winner (player 1) == payoff [1,-1]
   && winner (player 2) == payoff [-1,1]
   && winner (player 1) == payoff [2,-1,-1]
   && winner (player 2) == payoff [-1,2,-1]
   && winner (player 3) == payoff [-1,-1,2])
test_winner = oh

test_loser :
  so (loser (player 1) == payoff [0]
   && loser (player 1) == payoff [-1,1]
   && loser (player 2) == payoff [1,-1]
   && loser (player 1) == payoff [-2,1,1]
   && loser (player 2) == payoff [1,-2,1]
   && loser (player 3) == payoff [1,1,-2])
test_loser = oh

test_tie :
  so (tie == payoff [0]
   && tie == payoff [0,0]
   && tie == payoff [0,0,0])
test_tie = oh

test_showFloat :
  so (showFloat 0 == "0"
   && showFloat 1.0 == "1"
   && showFloat 2.5 == "2.5")
test_showFloat = oh

test_showPayoffAsList :
  so (showPayoffAsList [1,2,3,4.5] == "[1,2,3,4.5]")
test_showPayoffAsList = oh
