-- | Heterogeneous vectors of a shared collection type.
--   This module is adapted from Idris's standard Data.HVect.
module Data.HVectOf

import Data.HVect

%default total


--
-- * Representation
--

using (n : Nat, ts : Vect k Type, c : Type -> Type)
  
  -- | A heterogeneous vector of collection type `c`.
  data HVectOf : (Type -> Type) -> Vect k Type -> Type where
    Nil  : HVectOf c Nil
    (::) : c t -> HVectOf c ts -> HVectOf c (t :: ts)

  -- | Get the first collection in the vector.
  head : HVectOf c (t :: ts) -> c t
  head (xs :: xss) = xs
  
  -- | Pop the first collection in the vector.
  tail : HVectOf c (t :: ts) -> HVectOf c ts
  tail (xs :: xss) = xss

  instance Eq (HVectOf c Nil) where
    _ == _ = True

  instance (Eq (c t), Eq (HVectOf c ts)) => Eq (HVectOf c (t::ts)) where
    (x :: xs) == (y :: ys) = x == y && xs == ys

  -- TODO Add Show machinery?


--
-- * Indexing operations
--

  -- | Return the collection at index `i`.
  index : (i : Fin k) -> HVectOf c ts -> c (index i ts)
  index fZ     (x :: xs) = x
  index (fS j) (x :: xs) = index j xs
  
  -- | Delete the collection at index `i`.
  deleteAt : {us : Vect (S l) Type}
          -> (i : Fin (S l))
          -> HVectOf c us
          -> HVectOf c (deleteAt i us)
  deleteAt           fZ     (x :: xs) = xs
  deleteAt {l = S m} (fS j) (x :: xs) = x :: deleteAt j xs
  deleteAt           _      Nil       impossible

  -- | Replace the collection at index `i`.
  replaceAt : (i : Fin k)
           -> c t
           -> HVectOf c ts
           -> HVectOf c (replaceAt i t ts)
  replaceAt fZ     y (x :: xs) = y :: xs
  replaceAt (fS j) y (x :: xs) = x :: replaceAt j y xs

  -- | Update the collection at index `i`.
  updateAt : (i : Fin k)
          -> (c (index i ts) -> c t)
          -> HVectOf c ts
          -> HVectOf c (replaceAt i t ts)
  updateAt fZ     f (x :: xs) = f x :: xs
  updateAt (fS j) f (x :: xs) =   x :: updateAt j f xs

  -- | Concatenate two heterogeneous vectors.
  (++) : HVectOf c ts -> {us : Vect l Type} -> HVectOf c us -> HVectOf c (ts ++ us)
  (++) Nil       ys = ys
  (++) (x :: xs) ys = x :: (xs ++ ys)


--
-- * Heterogeneous vectors of lists
--
  
  -- | Computes the n-ary cartesian product of the lists within a heterogeneous
  --   vector of lists.
  --   For example:
  --   >> cartesian [[1,2,3],['a','b']]
  --   [[1,'a'],[1,'b'],[2,'a'],[2,'b'],[3,'a'],[3,'b']]
  cartesianProduct : HVectOf List ts -> List (HVect ts)
  cartesianProduct Nil       = [Nil]
  cartesianProduct (xs::xss) = concatMap (\x => map (x ::) (cartesianProduct xss)) xs


--
-- * Static unit tests
--

namespace Test
  
  test_cartesianProduct :
    so (cartesianProduct [[1,2,3],['a','b']]
          == [[1,'a'],[1,'b'],[2,'a'],[2,'b'],[3,'a'],[3,'b']])
  test_cartesianProduct = oh
