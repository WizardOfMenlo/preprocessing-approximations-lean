import Mathlib

open Polynomial Matrix
variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

theorem LatticePrepro.exists_det_submatrix_ne_zero [Fintype m] (A : Matrix m n K) {k : ℕ} (hk : A.rank = k) :
    ∃ (r : Fin k → m) (c : Fin k → n), (A.submatrix r c).det ≠ 0 := by sorry
