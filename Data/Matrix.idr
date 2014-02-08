module Data.Matrix

%default total


--
-- * Two-dimensional matrices
--

-- | A two-dimensional matrix of data.
Matrix : Nat -> Nat -> Type -> Type
Matrix rows cols a = Vect rows (Vect cols a)

-- | Build a matrix from a generator function.
buildMatrix : (Fin rows -> Fin cols -> a) -> Matrix rows cols a
buildMatrix f = map (\r => map (f r) range) range

-- | Lookup a value in a matrix.
index : Fin rows -> Fin cols -> Matrix rows cols a -> a
index r c = index c . index r

-- | Get a particular row of the matrix.
row : Fin rows -> Matrix rows cols a -> Vect cols a
row = index

-- | Get a particular column of the matrix.
col : Fin cols -> Matrix rows cols a -> Vect rows a
col = map . index


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
