module Data.HVectByOf

import Data.HVect
import Data.HVectOf

%default total


--
-- * X-indexed heterogeneous vectors of a shared collection type.
--

using (X : Nat -> Type, k : Nat, ts : Vect k Type, m : Type -> Type)
 
  -- | A heterogeneous vector of lists indexed by some type X.
  data HVectByOf : (Nat -> Type) -> (Type -> Type) -> Vect k Type -> Type where
    MkHVectByOf : HVectOf m ts -> HVectByOf X m ts

  -- | Convert a plain `HVectOf` into an X-indexed `HVectByOf`.
  fromHVectOf : HVectOf m ts -> HVectByOf X m ts
  fromHVectOf = MkHVectByOf

  -- | Convert an X-indexed `HVectByOf` into a plain `HVectOf`.
  toHVectOf : HVectByOf X m ts -> HVectOf m ts
  toHVectOf (MkHVectByOf v) = v

  -- | Index into an `HVectByOf` by casting X to a finite nat.
  for : Cast (X k) (Fin k) => 
        (x : X k) -> HVectByOf X m ts -> m (index (cast x) ts)
  for x (MkHVectByOf v) = index (cast x) v
  
  -- | Replace in an `HVectByOf`.
  replaceFor : Cast (X k) (Fin k) =>
               (x : X k) -> m t -> HVectByOf X m ts
            -> HVectByOf X m (replaceAt (cast x) t ts)
  replaceFor x l (MkHVectByOf v) = MkHVectByOf (replaceAt (cast x) l v)
 

  instance Eq (HVectByOf X m Nil) where
    _ == _ = True
  
  instance (Eq (m t), Eq (HVectByOf X m ts)) => Eq (HVectByOf X m (t :: ts)) where
    (MkHVectByOf (x :: xs)) == (MkHVectByOf (y :: ys)) =
        x == y && MkHVectByOf xs == MkHVectByOf ys
