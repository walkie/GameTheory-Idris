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

  -- | Replace in an X-indexed vector.
  replaceFor : Cast (X n) (Fin n) => X n -> a -> VectBy X n a -> VectBy X n a
  replaceFor x a (MkVectBy v) = MkVectBy (replaceAt (cast x) a v)

  -- | Update in an X-indexed vector.
  updateFor : Cast (X n) (Fin n) => X n -> (a -> a) -> VectBy X n a -> VectBy X n a
  updateFor x f (MkVectBy v) = MkVectBy (updateAt (cast x) f v)


  instance Eq a => Eq (VectBy X n a) where
    (MkVectBy v) == (MkVectBy v') = v == v'
  
  instance Functor (VectBy X n) where
    map f (MkVectBy v) = MkVectBy (map f v)
  
  instance Foldable (VectBy X n) where
    foldr f a (MkVectBy v) = foldr f a v
