import Mathlib

open Polynomial Matrix

theorem LatticePrepro.exists_dependence_of_rank_le {K : Type*} [Field K] {ℓ : ℕ} (A : Matrix (Fin ℓ) (Fin ℓ) K)
    {t : ℕ} (ht : A.rank ≤ t) (htℓ : t + 1 ≤ ℓ) :
    ∃ c : Fin (t + 1) → K, c ≠ 0 ∧ ∀ i : Fin ℓ, ∑ j, c j * A i (Fin.castLE htℓ j) = 0 := by sorry
