import LatticePrepro.Basic.Nat

/-!
# Generalized digits (Definition A.1, Claim A.2)

Moment orders are written as exponent vectors `η : Fin m → ℕ` with
`val B η = ∑ h, η h * B ^ h`. The *generalized digit vector* of `k` is obtained by writing
`k = a · (B^m - 1) + b` with `0 ≤ b < B^m - 1` and taking `a · (B - 1)` plus the base-`B`
digits of `b`. It satisfies `val B (gdigits B m k) = k`, and for `k ≤ J · (B^m - 1)` all its
entries are at most `J · (B - 1)`.
-/

namespace LatticePrepro

/-- `val B η = ∑ h, η h * B ^ h`. -/
def digitVal (B : ℕ) {m : ℕ} (η : Fin m → ℕ) : ℕ := ∑ h : Fin m, η h * B ^ (h : ℕ)

/-- The generalized digit vector of `k` (Definition A.1). -/
def gdigits (B m k : ℕ) : Fin m → ℕ :=
  fun h => (k / (B ^ m - 1)) * (B - 1) + (k % (B ^ m - 1)) / B ^ (h : ℕ) % B

lemma digitVal_add (B : ℕ) {m : ℕ} (η η' : Fin m → ℕ) :
    digitVal B (η + η') = digitVal B η + digitVal B η' := by
  simp [digitVal, add_mul, Finset.sum_add_distrib]

/-- Claim A.2, first part: `val B (gdigits B m k) = k`. -/
theorem digitVal_gdigits {B m : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) (k : ℕ) :
    digitVal B (gdigits B m k) = k := by
  have hn : 1 ≤ B ^ m - 1 := one_le_pow_sub_one hB hm
  set a := k / (B ^ m - 1) with ha
  set b := k % (B ^ m - 1) with hb
  have hbl : b < B ^ m := by
    have := Nat.mod_lt k (show 0 < B ^ m - 1 by omega)
    omega
  unfold digitVal gdigits
  rw [Fin.sum_univ_eq_sum_range (fun h => (a * (B - 1) + b / B ^ h % B) * B ^ h) m]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  rw [sum_digit_mul_pow, Nat.mod_eq_of_lt hbl, pred_mul_geomSum (by omega)]
  rw [ha, hb, Nat.div_add_mod']

/-- Claim A.2, second part: for `k ≤ J · (B^m - 1)`, every generalized digit is at most
`J · (B - 1)`. -/
theorem gdigits_le {B m J k : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) (hJ : 1 ≤ J)
    (hk : k ≤ J * (B ^ m - 1)) (h : Fin m) : gdigits B m k h ≤ J * (B - 1) := by
  have _ := hJ
  have hn : 1 ≤ B ^ m - 1 := one_le_pow_sub_one hB hm
  unfold gdigits
  have hdig : k % (B ^ m - 1) / B ^ (h : ℕ) % B ≤ B - 1 := by
    have := Nat.mod_lt (k % (B ^ m - 1) / B ^ (h : ℕ)) (show 0 < B by omega)
    omega
  have ha : k / (B ^ m - 1) ≤ J := Nat.div_le_of_le_mul (by rw [mul_comm]; exact hk)
  rcases Nat.lt_or_ge (k / (B ^ m - 1)) J with hlt | hge
  · calc k / (B ^ m - 1) * (B - 1) + k % (B ^ m - 1) / B ^ (h : ℕ) % B
        ≤ k / (B ^ m - 1) * (B - 1) + (B - 1) := Nat.add_le_add_left hdig _
      _ = (k / (B ^ m - 1) + 1) * (B - 1) := by ring
      _ ≤ J * (B - 1) := Nat.mul_le_mul_right _ hlt
  · have haJ : k / (B ^ m - 1) = J := le_antisymm ha hge
    have hkJ : k = J * (B ^ m - 1) := by
      have h1 : J * (B ^ m - 1) ≤ k := by
        rw [← haJ]; exact Nat.div_mul_le_self k (B ^ m - 1)
      omega
    have hb : k % (B ^ m - 1) = 0 := by rw [hkJ]; exact Nat.mul_mod_left _ _
    rw [haJ, hb, Nat.zero_div, Nat.zero_mod, add_zero]

/-- An exponent vector with entries at most `c · (B - 1)` has value at most `c · (B^m - 1)`. -/
theorem digitVal_le_of_le {B m c : ℕ} (hB : 2 ≤ B) (η : Fin m → ℕ)
    (hη : ∀ h, η h ≤ c * (B - 1)) : digitVal B η ≤ c * (B ^ m - 1) := by
  unfold digitVal
  calc ∑ h : Fin m, η h * B ^ (h : ℕ) ≤ ∑ h : Fin m, c * (B - 1) * B ^ (h : ℕ) :=
        Finset.sum_le_sum fun h _ => Nat.mul_le_mul_right _ (hη h)
    _ = c * ((B - 1) * ∑ h ∈ Finset.range m, B ^ h) := by
        rw [Fin.sum_univ_eq_sum_range (fun h => c * (B - 1) * B ^ h) m, Finset.mul_sum,
          Finset.mul_sum]
        simp only [mul_assoc]
    _ = c * (B ^ m - 1) := by rw [pred_mul_geomSum (by omega)]

end LatticePrepro
