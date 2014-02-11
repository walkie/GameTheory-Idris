-- | Heterogeneous vectors of a shared collection type.
--   This module is adapted from Idris's standard Data.HVect.
module Data.HVectOf

import Data.HVect

%default total


--
-- * Representation
--

using (n : Nat, ts : Vect k Type, m : Type -> Type)
  
  -- | A heterogeneous vector of collection type `m`.
  data HVectOf : (Type -> Type) -> Vect k Type -> Type where
    Nil  : HVectOf m Nil
    (::) : m t -> HVectOf m ts -> HVectOf m (t :: ts)

  -- | Get the first collection in the vector.
  head : HVectOf m (t :: ts) -> m t
  head (xs :: xss) = xs
  
  -- | Pop the first collection in the vector.
  tail : HVectOf m (t :: ts) -> HVectOf m ts
  tail (xs :: xss) = xss

  instance Eq (HVectOf m Nil) where
    _ == _ = True

  instance (Eq (m t), Eq (HVectOf m ts)) => Eq (HVectOf m (t::ts)) where
    (x :: xs) == (y :: ys) = x == y && xs == ys

  -- TODO Add Show machinery?


--
-- * Indexing operations
--

  -- | Return the collection at index `i`.
  index : (i : Fin k) -> HVectOf m ts -> m (index i ts)
  index fZ     (x :: xs) = x
  index (fS j) (x :: xs) = index j xs
  
  -- | Delete the collection at index `i`.
  deleteAt : {us : Vect (S l) Type}
          -> (i : Fin (S l))
          -> HVectOf m us
          -> HVectOf m (deleteAt i us)
  deleteAt           fZ     (x :: xs) = xs
  deleteAt {l = S m} (fS j) (x :: xs) = x :: deleteAt j xs
  deleteAt           _      Nil       impossible

  -- | Replace the collection at index `i`.
  replaceAt : (i : Fin k)
           -> m t
           -> HVectOf m ts
           -> HVectOf m (replaceAt i t ts)
  replaceAt fZ     y (x :: xs) = y :: xs
  replaceAt (fS j) y (x :: xs) = x :: replaceAt j y xs

  -- | Update the collection at index `i`.
  updateAt : (i : Fin k)
          -> (m (index i ts) -> m t)
          -> HVectOf m ts
          -> HVectOf m (replaceAt i t ts)
  updateAt fZ     f (x :: xs) = f x :: xs
  updateAt (fS j) f (x :: xs) =   x :: updateAt j f xs


--
-- * Heterogeneous vectors of lists
--
  
  -- | Concatenate two heterogeneous vectors of lists.
  (++) : HVectOf List ts -> {us : Vect l Type} -> HVectOf List us -> HVectOf List (ts ++ us)
  (++) Nil       ys = ys
  (++) (x :: xs) ys = x :: (xs ++ ys)

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
