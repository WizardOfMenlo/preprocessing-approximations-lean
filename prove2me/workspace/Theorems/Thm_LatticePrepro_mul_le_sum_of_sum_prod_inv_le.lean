import Mathlib

open Finset

theorem LatticePrepro.mul_le_sum_of_sum_prod_inv_le {R : Type*} [Fintype R] {q : ℕ} (lam : R → Fin q → ℝ)
    (hlam : ∀ r j, 0 < lam r j) {t : ℝ} (ht : 0 < t)
    (h : (∑ r, ∏ j, (lam r j)⁻¹) * t ^ q ≤ Fintype.card R) :
    (Fintype.card R : ℝ) * q * t ≤ ∑ r, ∑ j, lam r j := by sorry
