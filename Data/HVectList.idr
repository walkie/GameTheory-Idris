-- | Heterogeneous vectors of lists. This module is adapted from Idris's
--   standard Data.HVect.
--
--   TODO This module could be generalized at least to arbitrary Monoids.
module Data.HVectList

import Data.HVect

%default total


--
-- * Heterogeneous vectors of lists
--

using (n : Nat, ts : Vect n Type)
  
  -- | A heterogeneous vector of lists.
  data HVectList : Vect n Type -> Type where
    Nil  : HVectList Nil
    (::) : List t -> HVectList ts -> HVectList (t :: ts)

  -- | Get the first list in the vector.
  head : HVectList (t :: ts) -> List t
  head (xs :: xss) = xs
  
  -- | Pop the first list in the vector.
  tail : HVectList (t :: ts) -> HVectList ts
  tail (xs :: xss) = xss

  -- | Return the list at index 'i'.
  index : (i : Fin n) -> HVectList ts -> List (index i ts)
  index fZ     (x :: xs) = x
  index (fS j) (x :: xs) = index j xs
  
  -- | Delete the list at index 'i'.
  deleteAt : {us : Vect (S l) Type}
          -> (i : Fin (S l))
          -> HVectList us
          -> HVectList (deleteAt i us)
  deleteAt           fZ     (x :: xs) = xs
  deleteAt {l = S m} (fS j) (x :: xs) = x :: deleteAt j xs
  deleteAt           _      Nil       impossible

  -- | Replace the list at index 'i'.
  replaceAt : (i : Fin n)
           -> List t
           -> HVectList ts
           -> HVectList (replaceAt i t ts)
  replaceAt fZ     y (x :: xs) = y :: xs
  replaceAt (fS j) y (x :: xs) = x :: replaceAt j y xs

  -- | Update the list at index 'i'.
  updateAt : (i : Fin n)
          -> (List (index i ts) -> List t)
          -> HVectList ts
          -> HVectList (replaceAt i t ts)
  updateAt fZ     f (x :: xs) = f x :: xs
  updateAt (fS j) f (x :: xs) =   x :: updateAt j f xs

  -- | Concatenate to heterogeneous vectors of lists.
  (++) : {us : Vect l Type} -> HVectList ts -> HVectList us -> HVectList (ts ++ us)
  (++) []        ys = ys
  (++) (x :: xs) ys = x :: (xs ++ ys)

  instance Eq (HVectList Nil) where
    _ == _ = True

  instance (Eq t, Eq (HVectList ts)) => Eq (HVectList (t::ts)) where
    (x :: xs) == (y :: ys) = x == y && xs == ys

  -- TODO Add Show machinery?
