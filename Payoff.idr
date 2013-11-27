-- | The outcome of a game is a payoff.  This module provides a simple
--   representation of payoffs, smart constructors for building typical
--   payoffs, and functions for pretty printing them.
module Payoff

import Data.Floats

import VectBy

%default total

--
-- * Representation
--

-- | Payoffs are represented as a vector of `Float` values where each value
--   corresponds to a particular player.
--   While the type of payoffs could be generalized, this representation
--   supports both cardinal and ordinal payoffs while being easy to work with.
Payoff : Nat -> Type
Payoff n = ByPlayer n Float


--
-- * Smart constructors
--

-- | Payoff where all players score payoff a, except player p, who scores b.
allBut : PlayerID n -> Float -> Float -> Payoff n
allBut p a b = replaceAt (cast p) b (replicate _ a)

-- | Zero-sum payoff where player p wins (scoring n-1) 
--   and all other players lose (scoring -1).
winner : PlayerID n -> Payoff n
winner {n} p = allBut p (-1) (fromInteger (cast n) - 1)

-- | Zero-sum payoff where player p wins (scoring n-1) 
--   and all other players lose (scoring -1).
loser : PlayerID n -> Payoff n
loser {n} p = allBut p 1 (1 - fromInteger (cast n))

-- | Zero-sum payoff where all players tie. Each player scores 0.
tie : Payoff n
tie = replicate _ 0


--
-- * Pretty printing
--

-- | Pretty print floats as integers, when possible.
showFloat : Float -> String
showFloat f = if f == floor f then fst (break (== '.') s) else s
  where s = show f

{-
-- | String representation of a Payoff.
showPayoff :: Payoff -> String
showPayoff (ByPlayer vs) = showSeq (map showFloat vs)

-- | Bracketed string representation of a Payoff.
showPayoffAsList :: Payoff -> String
showPayoffAsList p = "[" ++ showPayoff p ++ "]"
-}
