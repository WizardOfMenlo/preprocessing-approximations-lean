import LatticePrepro.Tables.Construction
import LatticePrepro.Tables.PolyMatrixRank

/-!
# Soundness of the explicit tables: the polynomial matrix (Definition A.5, Lemma A.5)

For a table `y` satisfying the constraints, the *polynomial matrix* `Hmat y` has entries
`P^y_{digits(h) + digits(h')} ∈ 𝕊[X]` (`0 ≤ h, h' < ℓ`, `ℓ = p (B^m - 1) + 1`). We show:

* its entries have degree `≤ Δ` (low-degree constraints);
* `Hmat y (s) = E · diag(y(·, s)) · Eᵀ`, so `∑_s rank Hmat y (s) ≤ wt(y)`;
* `Hmat y (γ)` is the Hankel matrix `(M̂_{h+h'}(y))` (index-consistency constraints);
* hence, by `card_mul_rank_eval_le`, the Hankel matrix has rank `ρ` with `(q - Δ) ρ ≤ wt(y)`,
  and its first `ρ + 1` columns are linearly dependent.
-/

namespace LatticePrepro

open Polynomial Matrix

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

/-- The Hankel length `ℓ = p (B^m - 1) + 1` (this is `hankelLen p (B^m)`). -/
def hLen (p m B : ℕ) : ℕ := p * (B ^ m - 1) + 1

/-- The matrix `E` with entries `λ^{digits(h)}`. -/
noncomputable def Emat : Matrix (Fin (hLen p m B)) (Fin m → FS.𝕊) FS.𝕊 :=
  Matrix.of fun h lam => ∏ g, lam g ^ gdigits B m h.val g

/-- The polynomial matrix of a table (Definition A.5). -/
noncomputable def Hmat (y : Coord FS m → ZMod p) :
    Matrix (Fin (hLen p m B)) (Fin (hLen p m B)) FS.𝕊[X] :=
  Matrix.of fun h h' => interp FS m y (gdigits B m h.val + gdigits B m h'.val)

variable {FS m B}

lemma gdigits_hLen_le (hB : 2 ≤ B) (hm : 1 ≤ m) (h : Fin (hLen p m B)) (g : Fin m) :
    gdigits B m h.val g ≤ p * (B - 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).pos
  have hk : h.val ≤ p * (B ^ m - 1) := by
    have := h.isLt; unfold hLen at this; omega
  exact gdigits_le hB hm hp hk g

lemma hankelExp_le (hB : 2 ≤ B) (hm : 1 ≤ m) (h h' : Fin (hLen p m B)) (g : Fin m) :
    (gdigits B m h.val + gdigits B m h'.val) g ≤ 2 * p * (B - 1) := by
  have h1 := gdigits_hLen_le hB hm h g
  have h2 := gdigits_hLen_le hB hm h' g
  simp only [Pi.add_apply]
  rw [mul_assoc]; omega

/-- The exponent vector of a Hankel entry, as an index. -/
def hankelIdx (hB : 2 ≤ B) (hm : 1 ≤ m) (h h' : Fin (hLen p m B)) : IdxSet p m B :=
  IdxSet.ofNat (gdigits B m h.val + gdigits B m h'.val) (hankelExp_le hB hm h h')

lemma hankelIdx_toNat (hB : 2 ≤ B) (hm : 1 ≤ m) (h h' : Fin (hLen p m B)) :
    (hankelIdx hB hm h h').toNat = gdigits B m h.val + gdigits B m h'.val :=
  IdxSet.toNat_ofNat _ _

/-- Entries of the polynomial matrix have degree at most `Δ`. -/
lemma natDegree_Hmat_le (hB : 2 ≤ B) (hm : 1 ≤ m) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (h h' : Fin (hLen p m B)) :
    (Hmat FS m B y h h').natDegree ≤ degBound p m B δ := by
  have := natDegree_interp_le_of_constraint hy (hankelIdx hB hm h h')
  rwa [hankelIdx_toNat] at this

/-- Evaluating the polynomial matrix at a node `s` gives `E · diag(y(·, s)) · Eᵀ`. -/
lemma Hmat_map_eval (y : Coord FS m → ZMod p) (s : FS.𝕊) :
    (Hmat FS m B y).map (eval s) =
      Emat FS m B * Matrix.diagonal (fun lam => algebraMap (ZMod p) FS.𝕊 (y (lam, s))) *
        (Emat FS m B)ᵀ := by
  ext h h'
  simp only [Hmat, Matrix.map_apply, Matrix.of_apply, eval_interp, colSum]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Emat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [Algebra.smul_def]
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  ring

/-- The rank of `Hmat y (s)` is at most the weight of column `s`. -/
lemma rank_Hmat_map_eval_le (y : Coord FS m → ZMod p) (s : FS.𝕊) :
    ((Hmat FS m B y).map (eval s)).rank ≤ (Finset.univ.filter fun lam => y (lam, s) ≠ 0).card := by
  classical
  rw [Hmat_map_eval]
  calc (Emat FS m B * Matrix.diagonal (fun lam => algebraMap (ZMod p) FS.𝕊 (y (lam, s))) *
        (Emat FS m B)ᵀ).rank
      ≤ (Emat FS m B * Matrix.diagonal (fun lam => algebraMap (ZMod p) FS.𝕊 (y (lam, s)))).rank :=
        Matrix.rank_mul_le_left _ _
    _ ≤ (Matrix.diagonal (fun lam => algebraMap (ZMod p) FS.𝕊 (y (lam, s)))).rank :=
        Matrix.rank_mul_le_right _ _
    _ = Fintype.card {lam // algebraMap (ZMod p) FS.𝕊 (y (lam, s)) ≠ 0} := Matrix.rank_diagonal _
    _ = (Finset.univ.filter fun lam => y (lam, s) ≠ 0).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext lam
        simp [(algebraMap (ZMod p) FS.𝕊).injective.eq_iff' (map_zero _)]

/-- The Hamming weight is the sum of the column weights. -/
lemma hammingNorm_eq_sum_cols (y : Coord FS m → ZMod p) :
    hammingNorm y = ∑ s : FS.𝕊, (Finset.univ.filter fun lam => y (lam, s) ≠ 0).card := by
  classical
  unfold hammingNorm
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.card_bij (fun c _ => c.1) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [← hc.2]; exact hc.1
  · intro c hc c' hc' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    exact Prod.ext h (hc.2.trans hc'.2.symm)
  · intro lam hlam
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam
    exact ⟨(lam, s), by simpa using hlam, rfl⟩

lemma sum_rank_Hmat_map_eval_le (y : Coord FS m → ZMod p) :
    ∑ s : FS.𝕊, ((Hmat FS m B y).map (eval s)).rank ≤ hammingNorm y := by
  rw [hammingNorm_eq_sum_cols]
  exact Finset.sum_le_sum fun s _ => rank_Hmat_map_eval_le y s

/-- Evaluating the polynomial matrix at `γ` gives the Hankel matrix of the moments. -/
lemma Hmat_map_aeval (hB : 2 ≤ B) (hm : 1 ≤ m) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (h h' : Fin (hLen p m B)) :
    ((Hmat FS m B y).map (aeval FS.γ)) h h' = mom FS m B y (h.val + h'.val) := by
  simp only [Hmat, Matrix.map_apply, Matrix.of_apply]
  have := aeval_interp_eq_mom_of_constraint hy (hankelIdx hB hm h h')
  rw [hankelIdx_toNat, digitVal_add, digitVal_gdigits hB hm, digitVal_gdigits hB hm] at this
  exact this

/-- The rank inequality `q ρ ≤ wt(y) + Δ ρ` for the Hankel matrix. -/
lemma card_mul_rank_hankel_le (hB : 2 ≤ B) (hm : 1 ≤ m) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) :
    Fintype.card FS.𝕊 * ((Hmat FS m B y).map (aeval FS.γ)).rank ≤
      hammingNorm y + degBound p m B δ * ((Hmat FS m B y).map (aeval FS.γ)).rank := by
  have := card_mul_rank_eval_le FS.γ (Hmat FS m B y) (natDegree_Hmat_le hB hm hy)
  exact this.trans (Nat.add_le_add_right (sum_rank_Hmat_map_eval_le y) _)

/-- A square matrix of rank `≤ t < ℓ` has linearly dependent first `t + 1` columns. -/
lemma exists_dependence_of_rank_le {K : Type*} [Field K] {ℓ : ℕ} (A : Matrix (Fin ℓ) (Fin ℓ) K)
    {t : ℕ} (ht : A.rank ≤ t) (htℓ : t + 1 ≤ ℓ) :
    ∃ c : Fin (t + 1) → K, c ≠ 0 ∧ ∀ i : Fin ℓ, ∑ j, c j * A i (Fin.castLE htℓ j) = 0 := by
  classical
  set V := Submodule.span K (Set.range A.col) with hV
  have hfin : Module.finrank K V = A.rank := (Matrix.rank_eq_finrank_span_cols A).symm
  have : Module.Finite K V := Module.Finite.span_of_finite K (Set.finite_range _)
  let v : Fin (t + 1) → V := fun j => ⟨A.col (Fin.castLE htℓ j), Submodule.subset_span ⟨_, rfl⟩⟩
  have hv : ¬ LinearIndependent K v := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [hfin, Fintype.card_fin] at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hv
  obtain ⟨g, hg, i₀, hi₀⟩ := hv
  refine ⟨g, fun h => hi₀ (by simp [h]), fun i => ?_⟩
  have := congrArg (fun w : V => (w : Fin ℓ → K) i) hg
  simp only [v, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    Matrix.col, Matrix.transpose_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply] at this
  exact this

/-- **Soundness setup**: for a constrained table of weight below the threshold, the Hankel
matrix of its moments has rank `t < B^m` with `q t ≤ 2 wt(y)`, and its first `t + 1` columns
are linearly dependent. -/
theorem soundness_setup (hB : 2 ≤ B) (hm : 1 ≤ m)
    (hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (hw : 2 * hammingNorm y < B ^ m * Fintype.card FS.𝕊) :
    ∃ t : ℕ, t < B ^ m ∧ Fintype.card FS.𝕊 * t ≤ 2 * hammingNorm y ∧
      ∃ c : Fin (t + 1) → FS.K, c ≠ 0 ∧
        ∀ i : Fin (hLen p m B), ∑ j, c j * mom FS m B y (i.val + j.val) = 0 := by
  set q := Fintype.card FS.𝕊 with hq
  set Δ := degBound p m B δ with hΔdef
  set ρ := ((Hmat FS m B y).map (aeval FS.γ)).rank with hρ
  set w := hammingNorm y with hwdef
  have h1 : q * ρ ≤ w + Δ * ρ := card_mul_rank_hankel_le hB hm hy
  have h4 : 4 * (Δ * ρ) ≤ q * ρ := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right ρ hΔ.le
  have h3 : 3 * (q * ρ) ≤ 4 * w := by omega
  have hqρ : q * ρ ≤ 2 * w := by omega
  have hρr : ρ < B ^ m := by
    have h5 : (3 * ρ) * q < (2 * B ^ m) * q := by
      calc (3 * ρ) * q = 3 * (q * ρ) := by ring
        _ ≤ 4 * w := h3
        _ < 2 * (B ^ m * q) := by omega
        _ = (2 * B ^ m) * q := by ring
    have := Nat.lt_of_mul_lt_mul_right h5
    omega
  have hp : 1 ≤ p := (Fact.out : p.Prime).pos
  have hrℓ : B ^ m ≤ hLen p m B := by
    unfold hLen
    have h1 : 1 ≤ B ^ m := Nat.one_le_pow _ _ (by omega)
    have : B ^ m - 1 ≤ p * (B ^ m - 1) := Nat.le_mul_of_pos_left _ hp
    omega
  have htℓ : ρ + 1 ≤ hLen p m B := by omega
  refine ⟨ρ, hρr, hqρ, ?_⟩
  obtain ⟨c, hc, hdep⟩ := exists_dependence_of_rank_le ((Hmat FS m B y).map (aeval FS.γ)) le_rfl htℓ
  refine ⟨c, hc, fun i => ?_⟩
  have := hdep i
  simp only [Hmat_map_aeval hB hm hy, Fin.val_castLE] at this
  exact this

end ExplicitTables

end LatticePrepro
