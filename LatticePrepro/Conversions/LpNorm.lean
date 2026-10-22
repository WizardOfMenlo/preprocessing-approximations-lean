import Mathlib

/-!
# `ℓ_q` norms on finite real vectors

Elementary facts about `lpNorm q v = (∑ i, |v i| ^ q) ^ (1 / q)` and `supNorm v = ⨆ i, |v i|`
used in the lattice conversion:

* counting lemmas for integer vectors (`hammingNorm_le_sum_abs_rpow`);
* the power-mean / Hölder comparison `∑ v_i² ≤ N^{1 - 2/q} (∑ |v_i|^q)^{2/q}` for `q ≥ 2`
  (`sum_sq_le_card_rpow_mul_lpNorm_sq`), and `∑ v_i² ≤ N · (sup |v_i|)²`.
-/

namespace LatticePrepro

open Finset

variable {M : Type*} [Fintype M]

/-- The `ℓ_q` norm `(∑ i, |v i| ^ q) ^ (1 / q)` of a real vector. -/
noncomputable def lpNorm (q : ℝ) (v : M → ℝ) : ℝ := (∑ i, |v i| ^ q) ^ (1 / q)

/-- The sup norm `⨆ i, |v i|` of a real vector. -/
noncomputable def supNorm (v : M → ℝ) : ℝ := ⨆ i, |v i|

lemma sum_abs_rpow_nonneg (q : ℝ) (v : M → ℝ) : 0 ≤ ∑ i, |v i| ^ q :=
  sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

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

/-- For an integer vector, the number of nonzero coordinates is at most `∑ |v i| ^ q`
(`q ≥ 0`). -/
lemma card_ne_zero_le_sum_abs_rpow {q : ℝ} (hq : 0 ≤ q) (v : M → ℤ) :
    (((univ.filter fun i => v i ≠ 0).card : ℕ) : ℝ) ≤ ∑ i, |(v i : ℝ)| ^ q := by
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_le_sum fun i _ => ?_
  split_ifs with h
  · have h1 : (1 : ℝ) ≤ |(v i : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h
    exact_mod_cast Real.one_le_rpow h1 hq
  · exact Real.rpow_nonneg (abs_nonneg _) _

/-- For an integer vector, the number of nonzero coordinates is at most `∑ (v i)^2`. -/
lemma card_ne_zero_le_sum_sq (v : M → ℤ) :
    (((univ.filter fun i => v i ≠ 0).card : ℕ) : ℝ) ≤ ∑ i, ((v i : ℝ)) ^ 2 := by
  have := card_ne_zero_le_sum_abs_rpow (q := 2) (by norm_num) v
  simpa [Real.rpow_two, sq_abs] using this

/-- For a vector with entries of absolute value at most `1`, `∑ |v i| ^ q` is at most the
number of nonzero coordinates (`q > 0`). -/
lemma sum_abs_rpow_le_card_ne_zero {q : ℝ} (hq : 0 < q) {v : M → ℝ} (hv : ∀ i, |v i| ≤ 1) :
    ∑ i, |v i| ^ q ≤ (((univ.filter fun i => v i ≠ 0).card : ℕ) : ℝ) := by
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_le_sum fun i _ => ?_
  split_ifs with h
  · exact_mod_cast Real.rpow_le_one (abs_nonneg _) (hv i) hq.le
  · have h0 : v i = 0 := by simpa using h
    rw [h0, abs_zero, Real.zero_rpow hq.ne']

/-- Power-mean inequality: for `q ≥ 2`,
`∑ v_i² ≤ N ^ (1 - 2/q) · (∑ |v_i|^q) ^ (2/q)` where `N = |M|`. -/
lemma sum_sq_le_card_rpow_mul {q : ℝ} (hq : 2 ≤ q) (v : M → ℝ) :
    ∑ i, (v i) ^ 2 ≤ (Fintype.card M : ℝ) ^ (1 - 2 / q) * (∑ i, |v i| ^ q) ^ (2 / q) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [univ_eq_empty, sum_empty, Fintype.card_eq_zero, Nat.cast_zero]
    positivity
  have hq0 : 0 < q := by linarith
  set N : ℝ := (Fintype.card M : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  -- power mean with weights `1/N` and exponent `q/2 ≥ 1`
  have hpm := Real.rpow_arith_mean_le_arith_mean_rpow (s := univ) (fun _ => 1 / N)
    (fun i => (v i) ^ 2) (fun _ _ => by positivity)
    (by simp [hN, Finset.sum_const, Finset.card_univ])
    (fun i _ => sq_nonneg _) (p := q / 2) (by linarith)
  have hz : ∀ i, ((v i) ^ 2) ^ (q / 2) = |v i| ^ q := by
    intro i
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  simp only [hz] at hpm
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hpm
  -- raise to the power `2/q`
  have h2q : 0 ≤ 2 / q := by positivity
  have hA : 0 ≤ ∑ i, (v i) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, |v i| ^ q := sum_abs_rpow_nonneg q v
  have hmono := Real.rpow_le_rpow (by positivity) hpm h2q
  rw [← Real.rpow_mul (by positivity), show q / 2 * (2 / q) = 1 by field_simp, Real.rpow_one,
    Real.mul_rpow (by positivity) hB] at hmono
  -- `hmono : 1/N * A ≤ (1/N)^(2/q) * B^(2/q)`
  have hN' : N ^ (1 - 2 / q) = N * (1 / N) ^ (2 / q) := by
    rw [Real.rpow_sub hNpos, Real.rpow_one, one_div, Real.inv_rpow hNpos.le, div_eq_mul_inv]
  rw [hN']
  calc ∑ i, (v i) ^ 2 = N * (1 / N * ∑ i, (v i) ^ 2) := by field_simp
    _ ≤ N * ((1 / N) ^ (2 / q) * (∑ i, |v i| ^ q) ^ (2 / q)) :=
        mul_le_mul_of_nonneg_left hmono hNpos.le
    _ = N * (1 / N) ^ (2 / q) * (∑ i, |v i| ^ q) ^ (2 / q) := by ring

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
