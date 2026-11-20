import LatticePrepro.Basic.RealSums

/-!
# `ℓ_q` norms on finite real vectors

Elementary facts about `lpNorm q v = (∑ i, |v i| ^ q) ^ (1 / q)` and `supNorm v = ⨆ i, |v i|`
used in the lattice conversion. The counting lemmas for integer vectors and the power-mean
comparison live in `Basic/RealSums.lean`.
-/

namespace LatticePrepro

open Finset

variable {M : Type*} [Fintype M]

/-- The `ℓ_q` norm `(∑ i, |v i| ^ q) ^ (1 / q)` of a real vector. -/
noncomputable def lpNorm (q : ℝ) (v : M → ℝ) : ℝ := (∑ i, |v i| ^ q) ^ (1 / q)

/-- The sup norm `⨆ i, |v i|` of a real vector. -/
noncomputable def supNorm (v : M → ℝ) : ℝ := ⨆ i, |v i|

lemma lpNorm_nonneg (q : ℝ) (v : M → ℝ) : 0 ≤ lpNorm q v :=
  Real.rpow_nonneg (sum_abs_rpow_nonneg q v) _

lemma lpNorm_rpow {q : ℝ} (hq : 0 < q) (v : M → ℝ) : lpNorm q v ^ q = ∑ i, |v i| ^ q := by
  unfold lpNorm
  rw [one_div, Real.rpow_inv_rpow (sum_abs_rpow_nonneg q v) hq.ne']

/-- `‖v‖_q ^ 2 = (∑ |v i| ^ q) ^ (2 / q)`. -/
lemma lpNorm_sq (q : ℝ) (v : M → ℝ) :
    lpNorm q v ^ 2 = (∑ i, |v i| ^ q) ^ (2 / q) := by
  unfold lpNorm
  rw [← Real.rpow_natCast, ← Real.rpow_mul (sum_abs_rpow_nonneg q v)]
  congr 1
  push_cast
  ring

lemma lpNorm_le_rpow_of_sum_le {q : ℝ} (hq : 0 < q) {v : M → ℝ} {c : ℝ}
    (h : ∑ i, |v i| ^ q ≤ c) : lpNorm q v ≤ c ^ (1 / q) :=
  Real.rpow_le_rpow (sum_abs_rpow_nonneg q v) h (by positivity)

lemma abs_le_supNorm (v : M → ℝ) (i : M) : |v i| ≤ supNorm v := by
  unfold supNorm
  exact le_ciSup (Set.finite_range fun j => |v j|).bddAbove i

omit [Fintype M] in
lemma supNorm_nonneg (v : M → ℝ) : 0 ≤ supNorm v :=
  Real.iSup_nonneg fun _ => abs_nonneg _

omit [Fintype M] in
lemma supNorm_le {v : M → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, |v i| ≤ c) : supNorm v ≤ c :=
  Real.iSup_le h hc

/-- `∑ v_i² ≤ N · (sup |v_i|)²`. -/
lemma sum_sq_le_card_mul_supNorm_sq (v : M → ℝ) :
    ∑ i, (v i) ^ 2 ≤ (Fintype.card M : ℝ) * supNorm v ^ 2 := by
  calc ∑ i, (v i) ^ 2 ≤ ∑ _i : M, supNorm v ^ 2 := by
        refine sum_le_sum fun i _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_supNorm v i) 2
    _ = (Fintype.card M : ℝ) * supNorm v ^ 2 := by
        rw [sum_const, card_univ, nsmul_eq_mul]

end LatticePrepro
