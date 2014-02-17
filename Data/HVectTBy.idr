module Data.HVectTBy

import Data.HVectT

%default total


--
-- * X-indexed heterogeneous vectors of a shared collection type.
--

using (X : Nat -> Type, ts : Vect k Type, c : Type -> Type)
 
  -- | A heterogeneous vector of lists indexed by some type X.
  data HVectTBy : (Nat -> Type) -> (Type -> Type) -> Vect k Type -> Type where
    MkHVectTBy : HVectT c ts -> HVectTBy X c ts

  -- | Convert a plain `HVectT` into an X-indexed `HVectTBy`.
  fromHVectT : HVectT c ts -> HVectTBy X c ts
  fromHVectT = MkHVectTBy

  -- | Convert an X-indexed `HVectTBy` into a plain `HVectT`.
  toHVectT : HVectTBy X c ts -> HVectT c ts
  toHVectT (MkHVectTBy v) = v

  -- | Index into an `HVectTBy` by casting X to a finite nat.
  for : Cast (X k) (Fin k) => 
        (x : X k) -> HVectTBy X c ts -> c (index (cast x) ts)
  for x (MkHVectTBy v) = index (cast x) v
  
  -- | Replace in an `HVectTBy`.
  replaceFor : Cast (X k) (Fin k) =>
               (x : X k) -> c t -> HVectTBy X c ts
            -> HVectTBy X c (replaceAt (cast x) t ts)
  replaceFor x l (MkHVectTBy v) = MkHVectTBy (replaceAt (cast x) l v)

  -- | Update in an `HVectTBy`.
  updateFor : Cast (X k) (Fin k) =>
              (x : X k)
           -> (c (index (cast x) ts) -> c u)
           -> HVectTBy X c ts
           -> HVectTBy X c (replaceAt (cast x) u ts)
  updateFor x f (MkHVectTBy v) = MkHVectTBy (updateAt (cast x) f v)


  instance Eq (HVectTBy X c Nil) where
    _ == _ = True
  
  instance (Eq (c t), Eq (HVectTBy X c ts)) => Eq (HVectTBy X c (t :: ts)) where
    (MkHVectTBy (x :: xs)) == (MkHVectTBy (y :: ys)) =
        x == y && MkHVectTBy xs == MkHVectTBy ys
