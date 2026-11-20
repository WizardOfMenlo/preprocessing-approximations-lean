import Mathlib

/-!
# Generic facts about matrices and polynomial matrices

Mathlib-style lemmas with no dependence on the rest of the development:

* the degree of the determinant of a polynomial matrix with entries of degree `≤ Δ`;
* a matrix of rank `k` has a nonzero `k × k` minor;
* a square matrix of rank `b` can be brought to a form with `|n| - b` zero rows by an invertible
  matrix, and `(X - s)^{|n| - rank M(s)}` divides `det M` for a polynomial matrix `M`;
* a square matrix of rank `≤ t < ℓ` has linearly dependent first `t + 1` columns.
-/

namespace LatticePrepro

open Polynomial Matrix

section DetDegree

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of a polynomial matrix with entries of degree `≤ Δ` has degree
`≤ |n| · Δ`. -/
theorem natDegree_det_le_of_natDegree_le (A : Matrix n n R[X]) {Δ : ℕ}
    (h : ∀ i j, (A i j).natDegree ≤ Δ) : A.det.natDegree ≤ Fintype.card n * Δ := by
  rw [Matrix.det_apply']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_intCast, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le Finset.univ _) ?_
  calc ∑ i, (A (σ i) i).natDegree ≤ ∑ _i : n, Δ := Finset.sum_le_sum fun i _ => h _ _
    _ = Fintype.card n * Δ := by simp

end DetDegree

section Minor

variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

/-- From a matrix of rank `k` one can pick `k` linearly independent columns. -/
theorem exists_linearIndependent_cols (A : Matrix m n K) {k : ℕ} (hk : A.rank = k) :
    ∃ c : Fin k → n, LinearIndependent K (fun j => A.col (c j)) := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range A.col)
  have hbfin : b.Finite := (Set.finite_range A.col).subset hb
  have : Fintype b := hbfin.fintype
  have hcard : Fintype.card b = k := by
    have h1 := finrank_span_eq_card (R := K) hli
    rw [Subtype.range_coe, hspan, ← Matrix.rank_eq_finrank_span_cols, hk] at h1
    exact h1.symm
  let e : Fin k ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hchoice : ∀ x : b, ∃ j, A.col j = x := fun x => hb x.2
  choose c hc using hchoice
  refine ⟨fun j => c (e j), ?_⟩
  have : (fun j => A.col (c (e j))) = fun j => ((e j : b) : m → K) := by
    funext j; exact hc (e j)
  rw [this]
  exact hli.comp e e.injective

/-- A matrix with linearly independent columns has rank equal to its number of columns. -/
theorem rank_eq_card_of_linearIndependent_cols (A : Matrix m n K)
    (h : LinearIndependent K A.col) : A.rank = Fintype.card n := by
  rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card h]

/-- A matrix of rank `k` has a nonzero `k × k` minor. -/
theorem exists_det_submatrix_ne_zero [Fintype m] (A : Matrix m n K) {k : ℕ} (hk : A.rank = k) :
    ∃ (r : Fin k → m) (c : Fin k → n), (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_linearIndependent_cols A hk
  set N : Matrix m (Fin k) K := A.submatrix id c with hN
  have hNcol : N.col = fun j => A.col (c j) := by
    funext j; ext i; rfl
  have hNrank : N.rank = k := by
    rw [rank_eq_card_of_linearIndependent_cols N (hNcol ▸ hc), Fintype.card_fin]
  have hNt : Nᵀ.rank = k := by rw [Matrix.rank_transpose, hNrank]
  obtain ⟨r, hr⟩ := exists_linearIndependent_cols Nᵀ hNt
  refine ⟨r, c, ?_⟩
  have hrows : LinearIndependent K (A.submatrix r c).row := by
    have : (A.submatrix r c).row = fun i => Nᵀ.col (r i) := by
      funext i; ext j; rfl
    rw [this]; exact hr
  have hunit : IsUnit (A.submatrix r c) := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end Minor

section ZeroRows

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix of rank `b` can be multiplied on the left by an invertible matrix so that
`|n| - b` of its rows vanish. -/
theorem exists_isUnit_mul_rows_eq_zero (B : Matrix n n K) :
    ∃ (U : Matrix n n K) (ι : Fin (Fintype.card n - B.rank) → n),
      IsUnit U.det ∧ Function.Injective ι ∧ ∀ k j, (U * B) (ι k) j = 0 := by
  obtain ⟨V, W, e, hV, hW, hVBW⟩ := Matrix.exists_rank_normal_form B
  refine ⟨V, fun k => e.symm (Sum.inr k), (Matrix.isUnit_iff_isUnit_det _).mp hV,
    fun a b hab => Sum.inr_injective (e.symm.injective hab), fun k j => ?_⟩
  have hWdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det _).mp hW
  have hVB : V * B = (fromBlocks 1 0 0 0).submatrix e e * W⁻¹ := by
    calc V * B = V * B * W * W⁻¹ := (Matrix.mul_nonsing_inv_cancel_right W (V * B) hWdet).symm
      _ = (fromBlocks 1 0 0 0).submatrix e e * W⁻¹ := by rw [hVBW]
  rw [hVB, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  rcases hx : e x with a | a
  · simp [Matrix.fromBlocks_apply₂₁]
  · simp [Matrix.fromBlocks_apply₂₂]

end ZeroRows

section Dvd

variable {𝕊 : Type*} [Field 𝕊] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a square polynomial matrix `M` and a point `s`, `(X - s)^{|n| - rank M(s)}` divides
`det M`. -/
theorem pow_X_sub_C_dvd_det (M : Matrix n n 𝕊[X]) (s : 𝕊) :
    (X - C s) ^ (Fintype.card n - (M.map (eval s)).rank) ∣ M.det := by
  classical
  set B := M.map (eval s) with hB
  obtain ⟨U, ι, hU, hι, hrows⟩ := exists_isUnit_mul_rows_eq_zero B
  set U' : Matrix n n 𝕊[X] := U.map C with hU'
  have hmap : (U' * M).map (eval s) = U * B := by
    have h1 := Matrix.map_mul (L := U') (M := M) (f := Polynomial.evalRingHom s)
    simp only [Polynomial.coe_evalRingHom] at h1
    rw [h1]
    congr 1
    ext i j
    simp [U', Matrix.map_apply]
  have hdvd : ∀ i j, i ∈ Finset.univ.image ι → ∃ q, (U' * M) i j = (X - C s) * q := by
    intro i j hi
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hi
    have hroot : X - C s ∣ (U' * M) (ι k) j := by
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      have := congrFun (congrFun hmap (ι k)) j
      simp only [Matrix.map_apply] at this
      rw [this]; exact hrows k j
    exact hroot
  choose! Q hQ using hdvd
  set Z : Finset n := Finset.univ.image ι with hZ
  let w : n → 𝕊[X] := fun i => if i ∈ Z then X - C s else 1
  let A' : Matrix n n 𝕊[X] := Matrix.of fun i j => if i ∈ Z then Q i j else (U' * M) i j
  have hfactor : U' * M = Matrix.of fun i j => w i * A' i j := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, w, A']
    split_ifs with hi
    · exact hQ i j hi
    · rw [one_mul]
  have hprod : ∏ i, w i = (X - C s) ^ (Fintype.card n - B.rank) := by
    simp only [w]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
      Finset.card_image_of_injective _ hι, Finset.card_univ, Fintype.card_fin]
  have hdet : (U' * M).det = (X - C s) ^ (Fintype.card n - B.rank) * A'.det := by
    rw [hfactor, Matrix.det_mul_column, hprod]
  have hdvd' : (X - C s) ^ (Fintype.card n - B.rank) ∣ (U' * M).det := ⟨A'.det, hdet⟩
  rw [Matrix.det_mul] at hdvd'
  have hU'det : IsUnit U'.det := by
    rw [hU', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Polynomial.isUnit_C.mpr hU
  exact (hU'det.dvd_mul_left).mp hdvd'

end Dvd

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

end LatticePrepro
