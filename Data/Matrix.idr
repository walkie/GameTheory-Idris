module Data.Matrix


--
-- * Two-dimensional matrices
--

-- | A two-dimensional matrix of data.
Matrix : Nat -> Nat -> Type -> Type
Matrix m n a = Vect m (Vect n a)

-- | Lookup a value in a matrix.
index : Fin m -> Fin n -> Matrix m n a -> a
index r c = index c . index r

-- | Build a matrix from a generator function.
buildMatrix : (Fin m -> Fin n -> a) -> Matrix m n a
buildMatrix f = map (\r => map (f r) range) range


--
-- * Static unit tests
--

namespace Test
  
  m : Matrix 2 3 Nat
  m = [[1,2,3],[4,5,6]]

  test_index :
    so (index 0 0 m == 1
     && index 0 1 m == 2
     && index 0 2 m == 3
     && index 1 0 m == 4
     && index 1 1 m == 5
     && index 1 2 m == 6)
  test_index = oh

  prop_index_buildMatrix :
    so (buildMatrix (\r,c => index r c m) == m)
  prop_index_buildMatrix = oh
