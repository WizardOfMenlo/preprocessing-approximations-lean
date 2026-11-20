import Mathlib

theorem LatticePrepro.exists_base {Y m : ℕ} (hm : 1 ≤ m) (hY : 1 ≤ Y) :
    ∃ B : ℕ, 2 ≤ B ∧ Y ≤ B ^ m ∧ B ^ m ≤ 2 ^ m * Y := by sorry
