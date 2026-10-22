import LatticePrepro.Tables.Construction

/-!
# Evaluation tables of field elements (Construction A.4, step 6; completeness in Theorem A.7)

For `α ∈ K` and `h < m`, let `ℓ_h ∈ 𝕊[X]` be the polynomial of degree `< δ` with
`ℓ_h(γ) = α^{B^h}`. The *element table* `ê_α` has a single `1` in every column `s`, at the label
`λ = (ℓ_0(s), …, ℓ_{m-1}(s))`. Its column sums are `∏_h ℓ_h(s)^{η_h}`, so its interpolants are the
low-degree polynomials `∏_h ℓ_h^{η_h}`, and its moments are `α^k`.
-/

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

/-- The polynomial `ℓ_h` with `ℓ_h(γ) = α^{B^h}` and degree `< δ`. -/
noncomputable def elemPoly (α : FS.K) (h : Fin m) : FS.𝕊[X] :=
  (FS.exists_aeval (α ^ B ^ (h : ℕ))).choose

lemma natDegree_elemPoly_lt (α : FS.K) (h : Fin m) : (elemPoly FS m B α h).natDegree < δ :=
  (FS.exists_aeval (α ^ B ^ (h : ℕ))).choose_spec.1

lemma aeval_elemPoly (α : FS.K) (h : Fin m) :
    aeval FS.γ (elemPoly FS m B α h) = α ^ B ^ (h : ℕ) :=
  (FS.exists_aeval (α ^ B ^ (h : ℕ))).choose_spec.2

/-- The label of `α` in column `s`. -/
noncomputable def elemLabel (α : FS.K) (s : FS.𝕊) : Fin m → FS.𝕊 :=
  fun h => eval s (elemPoly FS m B α h)

/-- The element table `ê_α`. -/
noncomputable def elemTab (α : FS.K) : Coord FS m → ZMod p :=
  fun ls => if ls.1 = elemLabel FS m B α ls.2 then 1 else 0

/-- The product polynomial `∏_h ℓ_h^{η_h}`. -/
noncomputable def elemProd (α : FS.K) (η : Fin m → ℕ) : FS.𝕊[X] :=
  ∏ h, elemPoly FS m B α h ^ η h

variable {FS m B}

lemma elemTab_binary (α : FS.K) : IsBinary (elemTab FS m B α) := by
  intro ls
  unfold elemTab
  split_ifs <;> simp

lemma blockSupport_elemTab (α : FS.K) (s : FS.𝕊) :
    blockSupport Prod.snd (elemTab FS m B α) s = {(elemLabel FS m B α s, s)} := by
  ext ⟨lam, s'⟩
  rw [blockSupport, Finset.mem_filter, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, h⟩
    refine ⟨?_, rfl⟩
    by_contra hne
    exact h (by simp [elemTab, hne])
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, by simp [elemTab]⟩

lemma elemTab_onePerBlock (α : FS.K) : ExactlyOnePerBlock Prod.snd (elemTab FS m B α) := by
  intro s
  rw [blockSupport_elemTab, Finset.card_singleton]

/-- The column sums of the element table. -/
lemma colSum_elemTab (α : FS.K) (η : Fin m → ℕ) (s : FS.𝕊) :
    colSum FS m (elemTab FS m B α) η s = ∏ h, elemLabel FS m B α s h ^ η h := by
  unfold colSum elemTab
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ (elemLabel FS m B α s)]
  simp

lemma natDegree_elemProd_le (α : FS.K) {η : Fin m → ℕ} (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    (elemProd FS m B α η).natDegree ≤ degBound p m B δ := by
  unfold elemProd degBound
  calc (∏ h, elemPoly FS m B α h ^ η h).natDegree
      ≤ ∑ h, (elemPoly FS m B α h ^ η h).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ h, η h * (elemPoly FS m B α h).natDegree :=
        Finset.sum_le_sum fun h _ => natDegree_pow_le
    _ ≤ ∑ _h : Fin m, 2 * p * (B - 1) * (δ - 1) := by
        refine Finset.sum_le_sum fun h _ => Nat.mul_le_mul (hη h) ?_
        have := natDegree_elemPoly_lt FS m B α h
        omega
    _ = 2 * p * m * (B - 1) * (δ - 1) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

lemma eval_elemProd (α : FS.K) (η : Fin m → ℕ) (s : FS.𝕊) :
    eval s (elemProd FS m B α η) = ∏ h, elemLabel FS m B α s h ^ η h := by
  unfold elemProd elemLabel
  simp [eval_prod, eval_pow]

lemma aeval_elemProd (α : FS.K) (η : Fin m → ℕ) :
    aeval FS.γ (elemProd FS m B α η) = α ^ digitVal B η := by
  unfold elemProd digitVal
  rw [map_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [map_pow, aeval_elemPoly, ← pow_mul, mul_comm]

/-- The interpolants of the element table are the product polynomials. -/
lemma interp_elemTab (hΔ : degBound p m B δ < Fintype.card FS.𝕊) (α : FS.K) {η : Fin m → ℕ}
    (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    interp FS m (elemTab FS m B α) η = elemProd FS m B α η := by
  apply interp_eq_of_eval_eq
  · calc (elemProd FS m B α η).degree ≤ (elemProd FS m B α η).natDegree := degree_le_natDegree
      _ < Fintype.card FS.𝕊 := by
        exact_mod_cast lt_of_le_of_lt (natDegree_elemProd_le α hη) hΔ
  · intro s
    rw [eval_elemProd, colSum_elemTab]

lemma aeval_interp_elemTab (hΔ : degBound p m B δ < Fintype.card FS.𝕊) (α : FS.K)
    {η : Fin m → ℕ} (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    aeval FS.γ (interp FS m (elemTab FS m B α) η) = α ^ digitVal B η := by
  rw [interp_elemTab hΔ α hη, aeval_elemProd]

/-- Generalized digits of admissible orders are admissible exponents. -/
lemma gdigits_le_of_le (hB : 2 ≤ B) (hm : 1 ≤ m) {k : ℕ} (hk : k ≤ 2 * p * (B ^ m - 1))
    (h : Fin m) : gdigits B m k h ≤ 2 * p * (B - 1) := by
  have hp : 1 ≤ 2 * p := by have := (Fact.out : p.Prime).pos; omega
  exact gdigits_le hB hm hp hk h

/-- The moments of the element table are the powers of `α`. -/
lemma mom_elemTab (hB : 2 ≤ B) (hm : 1 ≤ m) (hΔ : degBound p m B δ < Fintype.card FS.𝕊)
    (α : FS.K) {k : ℕ} (hk : k ≤ 2 * p * (B ^ m - 1)) :
    mom FS m B (elemTab FS m B α) k = α ^ k := by
  unfold mom
  rw [aeval_interp_elemTab hΔ α (gdigits_le_of_le hB hm hk), digitVal_gdigits hB hm]

/-- The element table satisfies the evaluation table constraints. -/
lemma constraintFun_elemTab (hB : 2 ≤ B) (hm : 1 ≤ m) (hΔ : degBound p m B δ < Fintype.card FS.𝕊)
    (α : FS.K) : constraintFun FS m B (elemTab FS m B α) = 0 := by
  have hval : ∀ η : IdxSet p m B, digitVal B η.toNat ≤ 2 * p * (B ^ m - 1) :=
    fun η => digitVal_le_of_le hB η.toNat η.toNat_le
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext ηu
    simp only [constraintFun, Pi.zero_apply, Prod.fst_zero]
    split_ifs with hu
    · rw [interp_elemTab hΔ α ηu.1.toNat_le]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_elemProd_le α ηu.1.toNat_le) hu)
    · rfl
  · funext η
    simp only [constraintFun, Pi.zero_apply, Prod.snd_zero, Prod.fst_zero]
    rw [aeval_interp_elemTab hΔ α η.toNat_le, mom_elemTab hB hm hΔ α (hval η), sub_self]
  · funext k
    simp only [constraintFun, Pi.zero_apply, Prod.snd_zero]
    split_ifs with hk
    · unfold maxOrder at hk
      have hp : 1 ≤ p := (Fact.out : p.Prime).pos
      have hk' : k.val ≤ 2 * p * (B ^ m - 1) :=
        le_trans (Nat.le_mul_of_pos_left k.val hp) hk
      rw [mom_elemTab hB hm hΔ α hk, mom_elemTab hB hm hΔ α hk', ← pow_mul, mul_comm, sub_self]
    · rfl

/-- **Completeness** of the explicit moment representation. -/
theorem elemTab_complete (hB : 2 ≤ B) (hm : 1 ≤ m) (hΔ : degBound p m B δ < Fintype.card FS.𝕊)
    (α : FS.K) :
    IsBinary (elemTab FS m B α) ∧ ExactlyOnePerBlock Prod.snd (elemTab FS m B α) ∧
      constraintFun FS m B (elemTab FS m B α) = 0 ∧
      ∀ k ≤ 2 * B ^ m - 2, mom FS m B (elemTab FS m B α) k = α ^ k := by
  refine ⟨elemTab_binary α, elemTab_onePerBlock α, constraintFun_elemTab hB hm hΔ α, ?_⟩
  intro k hk
  apply mom_elemTab hB hm hΔ α
  have hp : 1 ≤ p := (Fact.out : p.Prime).pos
  have h1 : 1 ≤ B ^ m := Nat.one_le_pow _ _ (by omega)
  calc k ≤ 2 * B ^ m - 2 := hk
    _ = 2 * (B ^ m - 1) := by omega
    _ ≤ 2 * p * (B ^ m - 1) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left _ hp)

end ExplicitTables

end LatticePrepro
