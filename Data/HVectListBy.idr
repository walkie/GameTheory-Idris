module Data.HVectListBy

import Data.HVect
import Data.HVectList

%default total


--
-- * X-indexed heterogeneous vectors of lists
--

using (X : Nat -> Type, n : Nat, ts : Vect n Type)
 
  -- | A heterogeneous vector of lists indexed by some type X.
  data HVectListBy : (Nat -> Type) -> Vect n Type -> Type where
    MkHVectListBy : HVectList ts -> HVectListBy X ts

  -- | Convert a plain 'HVectList' into an X-indexed 'HVectListBy'.
  fromHVectList : HVectList ts -> HVectListBy X ts
  fromHVectList = MkHVectListBy

  -- | Convert an X-indexed 'HVectListBy' into a plain 'HVectList'.
  toHVectList : HVectListBy X ts -> HVectList ts
  toHVectList (MkHVectListBy v) = v

  -- | Index into an 'HVectListBy' by casting X to a finite nat.
  for : Cast (X n) (Fin n) => 
        (x : X n) -> HVectListBy X ts -> List (index (cast x) ts)
  for x (MkHVectListBy v) = index (cast x) v
  
  instance Eq (HVectListBy X Nil) where
    _ == _ = True
  
  instance (Eq t, Eq (HVectListBy X ts)) => Eq (HVectListBy X (t :: ts)) where
    (MkHVectListBy (x :: xs)) == (MkHVectListBy (y :: ys)) =
        x == y && MkHVectListBy xs == MkHVectListBy ys
