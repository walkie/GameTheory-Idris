module Data.HVectBy

import Data.HVect

%default total

--
-- * X-indexed heterogeneous vectors
--

using (X : Nat -> Type, n : Nat, ts : Vect n Type)
  
  -- | A heterogeneous vector indexed by some type X.
  data HVectBy : (Nat -> Type) -> Vect n Type -> Type where
    MkHVectBy : HVect ts -> HVectBy X ts

  -- | Convert a plain h-vector into an X-indexed h-vector.
  fromHVect : HVect ts -> HVectBy X ts
  fromHVect = MkHVectBy

  -- | Convert an X-indexed h-vector into a plain h-vector.
  toHVect : HVectBy X ts -> HVect ts
  toHVect (MkHVectBy v) = v

  -- | Index into an X-indexed h-vector by casting X to a finite nat.
  for : Cast (X n) (Fin n) => 
        (x : X n) -> HVectBy X ts -> index (cast x) ts
  for x (MkHVectBy v) = index (cast x) v

  
  instance Eq (HVectBy X Nil) where
    _ == _ = True
  
  instance (Eq t, Eq (HVectBy X ts)) => Eq (HVectBy X (t :: ts)) where
    (MkHVectBy (x :: xs)) == (MkHVectBy (y :: ys)) =
        x == y && MkHVectBy xs == MkHVectBy ys
  
  instance Shows n ts => Show (HVectBy X ts) where
    show = show . toHVect