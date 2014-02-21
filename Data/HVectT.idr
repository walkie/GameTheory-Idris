--   Heterogeneous vectors where the type of each element is applied
--   to a shared type constructor `c`. For example, `HVectT List` is
--   a vector of lists that is heterogeneous in the element type of
--   each list.
--
--   This module is adapted from Idris's standard Data.HVect.
module Data.HVectT

import Control.Monad.Identity
import Data.HVect

%default total


--
-- * Representation
--

using (ts : Vect k Type, c : Type -> Type)
  
  -- | A heterogeneous vector of some collection type `c`.
  data HVectT : (Type -> Type) -> Vect k Type -> Type where
    Nil  : HVectT c Nil
    (::) : c t -> HVectT c ts -> HVectT c (t :: ts)

  -- | An alternative implementation of plain heterogeneous vectors.
  HVect' : Vect k Type -> Type
  HVect' = HVectT Identity

  -- | Get the first collection in the vector.
  head : HVectT c (t :: ts) -> c t
  head (xs :: xss) = xs
  
  -- | Pop the first collection in the vector.
  tail : HVectT c (t :: ts) -> HVectT c ts
  tail (xs :: xss) = xss

  instance Eq (HVectT c Nil) where
    _ == _ = True
  instance (Eq (c t), Eq (HVectT c ts)) => Eq (HVectT c (t::ts)) where
    (x :: xs) == (y :: ys) = x == y && xs == ys

  instance Show (HVectT c Nil) where
    show Nil = "[]"
  instance (Show (c t), Show (HVectT c ts)) => Show (HVectT c (t::ts)) where
    show (x :: xs) = show x ++ " :: " ++ show xs


--
-- * Indexing operations
--

  -- | Return the collection at index `i`.
  index : (i : Fin k) -> HVectT c ts -> c (index i ts)
  index fZ     (x :: xs) = x
  index (fS j) (x :: xs) = index j xs
  
  -- | Delete the collection at index `i`.
  deleteAt : {us : Vect (S l) Type}
          -> (i : Fin (S l))
          -> HVectT c us
          -> HVectT c (deleteAt i us)
  deleteAt           fZ     (x :: xs) = xs
  deleteAt {l = S m} (fS j) (x :: xs) = x :: deleteAt j xs
  deleteAt           _      Nil       impossible

  -- | Replace the collection at index `i`.
  replaceAt : (i : Fin k)
           -> c u
           -> HVectT c ts
           -> HVectT c (replaceAt i u ts)
  replaceAt fZ     y (x :: xs) = y :: xs
  replaceAt (fS j) y (x :: xs) = x :: replaceAt j y xs

  -- | Update the collection at index `i`.
  updateAt : (i : Fin k)
          -> (c (index i ts) -> c u)
          -> HVectT c ts
          -> HVectT c (replaceAt i u ts)
  updateAt fZ     f (x :: xs) = f x :: xs
  updateAt (fS j) f (x :: xs) =   x :: updateAt j f xs


--
-- * Other operations
--

  -- | Initialize a heterogeneous vector of collections.
  initialize : ((t : Type) -> c t) -> (ts : Vect k Type) -> HVectT c ts
  initialize f (t :: ts) = f t :: initialize f ts
  initialize _ Nil       = Nil

  -- | Concatenate two heterogeneous vectors of collections.
  (++) : HVectT c ts -> {us : Vect l Type} -> HVectT c us -> HVectT c (ts ++ us)
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
  cartesianProduct : HVectT List ts -> List (HVect ts)
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
