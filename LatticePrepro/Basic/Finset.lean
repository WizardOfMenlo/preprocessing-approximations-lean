import Mathlib

/-!
# Telescoping sums
-/

namespace LatticePrepro

variable {K : Type*} [AddCommGroup K]

/-- A telescoping sum over `Finset.Ico a b`. -/
lemma sum_Ico_telescope (f : ℕ → K) {a b : ℕ} (hab : a ≤ b) :
    ∑ m ∈ Finset.Ico a b, (f m - f (m - 1)) = f (b - 1) - f (a - 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih, Nat.add_sub_cancel]
    abel

end LatticePrepro
