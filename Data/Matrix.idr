module Data.Matrix


--
-- * Two-dimensional matrices
--

-- | A two-dimensional matrix of data.
Matrix : Nat -> Nat -> Type -> Type
Matrix rows cols a = Vect rows (Vect cols a)

-- | Lookup a value in a matrix.
index : Fin rows -> Fin cols -> Matrix rows cols a -> a
index r c = index c . index r

-- | Build a matrix from a generator function.
buildMatrix : (Fin rows -> Fin cols -> a) -> Matrix rows cols a
buildMatrix f = map (\r => map (f r) range) range


--
-- * Static unit tests
--

namespace Test
  
  t_m : Matrix 2 3 Nat
  t_m = [[1,2,3],[4,5,6]]

  test_index :
    so (index 0 0 t_m == 1
     && index 0 1 t_m == 2
     && index 0 2 t_m == 3
     && index 1 0 t_m == 4
     && index 1 1 t_m == 5
     && index 1 2 t_m == 6)
  test_index = oh

  prop_index_buildMatrix :
    so (buildMatrix (\r,c => index r c t_m) == t_m)
  prop_index_buildMatrix = oh
