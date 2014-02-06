-- | Various representations of normal form games, smart contructors for
--   creating them, and functions for analyzing them.
--
--   TODO Generalize to n-ary normal form games?
module Game.Normal

import Game.Payoff
import Game.Util


--
-- * Representation
--

-- | A two-player normal form game.
data Normal : Nat -> Nat -> Type -> Type -> Type where
  MkNormal : Vect n1 m1 -> Vect n2 m2 -> Vect (n1*n2) (Payoff 2) -> Normal n1 n2 m1 m2


--
-- * Smart Constructors
--

-- | Construct a two-player symmetric game.
symmetric : Vect (S n) m -> Vect (S n * S n) Float -> Normal (S n) (S n) m m
symmetric {n} ms vs = MkNormal ms ms (map pay range)
  where
    
    sym : Fin (S n * S n) -> Fin (S n * S n)
    sym i = if cast i == n2 then i else natToFin_ (mod (cast i * S n) n2)
      where n2 = S n * S n - 1
    
    pay : Fin (S n * S n) -> Payoff 2
    pay i = payoff [index i vs, index (sym i) vs]

-- | Construct a zero-sum payoff vector from a vector of floats.
zerosum : Vect n Float -> Vect n (Payoff 2)
zerosum = map (\v => payoff [v,-v])

-- | Construct a two-player zero-sum game. The payoffs are given from the
--   first player's perspective.
matrix : Vect n1 m1 -> Vect n2 m2 -> Vect (n1*n2) Float -> Normal n1 n2 m1 m2
matrix ms1 ms2 vs = MkNormal ms1 ms2 (zerosum vs)

-- | Construct a two-player symmetric zero-sum game.
square : Vect n m -> Vect (n*n) Float -> Normal n n m m
square ms vs = MkNormal ms ms (zerosum vs)
