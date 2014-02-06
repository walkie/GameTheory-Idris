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
    
-- | Construct a two-player symmetric game.
symmetric : Vect (S n) m -> Vect (S n * S n) Float -> Normal (S n) (S n) m m
symmetric {n} ms vs = MkNormal ms ms (map pay range)
  where
    
    sym : Fin (S n * S n) -> Fin (S n * S n)
    sym i = if cast i == n2 then i else natToFin_ (mod (cast i * S n) n2)
      where n2 = S n * S n - 1
    
    pay : Fin (S n * S n) -> Payoff 2
    pay i = payoff [index i vs, index (sym i) vs]
