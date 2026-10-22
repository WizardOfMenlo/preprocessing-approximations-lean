import Mathlib

/-!
# Elementary facts about natural numbers

Geometric sums and base-`B` digits without truncated subtraction, and the existence of bases and
powers in prescribed ranges.
-/

namespace LatticePrepro

/-- The geometric identity `(B - 1) · ∑_{h<m} B^h + 1 = B^m`, without subtraction. -/
lemma pred_mul_geomSum_add_one {B : ℕ} (hB : 1 ≤ B) (m : ℕ) :
    (B - 1) * (∑ h ∈ Finset.range m, B ^ h) + 1 = B ^ m := by
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, add_right_comm, ih, pow_succ]
    ring

/-- The geometric identity `(B - 1) · ∑_{h<m} B^h = B^m - 1`. -/
lemma pred_mul_geomSum {B : ℕ} (hB : 1 ≤ B) (m : ℕ) :
    (B - 1) * (∑ h ∈ Finset.range m, B ^ h) = B ^ m - 1 := by
  have := pred_mul_geomSum_add_one hB m
  omega

/-- The base-`B` digit expansion of `b` up to `m` digits recovers `b mod B^m`. -/
lemma sum_digit_mul_pow {B : ℕ} (b m : ℕ) :
    ∑ h ∈ Finset.range m, (b / B ^ h % B) * B ^ h = b % B ^ m := by
  induction m with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, mul_comm]

lemma one_le_pow_sub_one {B m : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) : 1 ≤ B ^ m - 1 := by
  have : B ≤ B ^ m := by
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ m := Nat.pow_le_pow_right (by omega) hm
  omega

/-- There is `B ≥ 2` with `Y ≤ B^m ≤ 2^m · Y` (the least `B ≥ 2` with `B^m ≥ Y`). -/
lemma exists_base {Y m : ℕ} (hm : 1 ≤ m) (hY : 1 ≤ Y) :
    ∃ B : ℕ, 2 ≤ B ∧ Y ≤ B ^ m ∧ B ^ m ≤ 2 ^ m * Y := by
  classical
  have hex : ∃ B : ℕ, 2 ≤ B ∧ Y ≤ B ^ m :=
    ⟨Y + 2, by omega, le_trans (by omega) (Nat.le_self_pow (by omega) (Y + 2))⟩
  set B := Nat.find hex with hBdef
  have hP : 2 ≤ B ∧ Y ≤ B ^ m := Nat.find_spec hex
  refine ⟨B, hP.1, hP.2, ?_⟩
  rcases Nat.lt_or_ge 2 B with h2 | h2
  · -- `B ≥ 3`: minimality gives `(B - 1)^m < Y`
    have hmin : ¬ (2 ≤ B - 1 ∧ Y ≤ (B - 1) ^ m) := Nat.find_min hex (by omega)
    have hlt : (B - 1) ^ m < Y := by
      by_contra hcon
      exact hmin ⟨by omega, not_lt.mp hcon⟩
    calc B ^ m ≤ (2 * (B - 1)) ^ m := Nat.pow_le_pow_left (by omega) m
      _ = 2 ^ m * (B - 1) ^ m := by rw [mul_pow]
      _ ≤ 2 ^ m * Y := Nat.mul_le_mul_left _ hlt.le
  · have hB2 : B = 2 := le_antisymm h2 hP.1
    rw [hB2]
    exact Nat.le_mul_of_pos_right _ hY

/-- A power of `p` in a prescribed range. -/
lemma exists_pow_between {p N : ℕ} (hp : 2 ≤ p) (hN : 2 ≤ N) :
    ∃ d, 1 ≤ d ∧ N ≤ p ^ d ∧ p ^ d < p * N := by
  classical
  have hex : ∃ d, N ≤ p ^ d := ⟨N, (Nat.lt_pow_self (by omega : 1 < p)).le⟩
  let d := Nat.find hex
  have hd : N ≤ p ^ d := Nat.find_spec hex
  have hd1 : 1 ≤ d := by
    by_contra h0
    have h0' : d = 0 := by omega
    rw [h0', pow_zero] at hd
    omega
  have hmin : ¬ N ≤ p ^ (d - 1) := Nat.find_min hex (by omega)
  refine ⟨d, hd1, hd, ?_⟩
  have hsplit : p ^ d = p * p ^ (d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit]
  exact (Nat.mul_lt_mul_left (by omega)).mpr (by omega)

end LatticePrepro
