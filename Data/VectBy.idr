module Data.VectBy

%default total


--
-- * X-indexed vectors
--

-- | A vector indexed by some type X.
data VectBy : (Nat -> Type) -> Nat -> Type -> Type where
  MkVectBy : {X : Nat -> Type} -> Vect n a -> VectBy X n a

using (X : Nat -> Type)

  -- | Convert a plain vector into an X-indexed vector.
  implicit
  fromVect : Vect n a -> VectBy X n a
  fromVect = MkVectBy

  -- | Convert an X-indexed vector into a plain vector.
  toVect : VectBy X n a -> Vect n a
  toVect (MkVectBy v) = v

  -- | Index into an X-indexed vector by casting X to a finite nat.
  for : Cast (X n) (Fin n) => X n -> VectBy X n a -> a
  for x (MkVectBy v) = index (cast x) v

  
  instance Eq a => Eq (VectBy X n a) where
    (MkVectBy v) == (MkVectBy v') = v == v'
  
  instance Functor (VectBy X n) where
    map f (MkVectBy v) = MkVectBy (map f v)
  
  instance Foldable (VectBy X n) where
    foldr f a (MkVectBy v) = foldr f a v
