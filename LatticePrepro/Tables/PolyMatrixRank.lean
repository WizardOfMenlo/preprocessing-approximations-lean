import Mathlib

/-!
# Rank of a polynomial matrix versus its evaluations (Lemma A.5, first part)

Let `H` be a square matrix over `𝕊[X]`, `𝕊` a finite field with `q` elements, whose entries have
degree at most `Δ`, and let `γ` be an element of an extension field `K` of `𝕊`. Then

`(q - Δ) · rank_K H(γ) ≤ ∑_{s ∈ 𝕊} rank_𝕊 H(s)`.

Proof sketch (Fancsali–Sziklai): let `ρ = rank_K H(γ)`; choose `ρ` rows and columns such that
the corresponding minor `M(X)` is nonzero at `γ` (hence a nonzero polynomial of degree `≤ ρΔ`).
For each `s`, bring `M(s)` to rank normal form by an invertible matrix `U`; then `ρ - rank M(s)`
rows of `U · M(X)` vanish at `s`, so `(X - s)^{ρ - rank M(s)}` divides `det M(X)`. The factors for
distinct `s` are coprime, so `∑_s (ρ - rank M(s)) ≤ deg det M(X) ≤ ρΔ`.
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

/-- **Lemma A.5 (rank bound)**, stated without natural-number subtraction:
`q · rank H(γ) ≤ ∑_s rank H(s) + Δ · rank H(γ)`. -/
theorem card_mul_rank_eval_le {𝕊 : Type*} [Field 𝕊] [Fintype 𝕊] [DecidableEq 𝕊]
    {K : Type*} [Field K] [Algebra 𝕊 K] (γ : K) {ℓ Δ : ℕ}
    (H : Matrix (Fin ℓ) (Fin ℓ) 𝕊[X]) (hdeg : ∀ i j, (H i j).natDegree ≤ Δ) :
    Fintype.card 𝕊 * (H.map (aeval γ)).rank ≤
      (∑ s : 𝕊, (H.map (eval s)).rank) + Δ * (H.map (aeval γ)).rank := by
  classical
  set ρ := (H.map (aeval γ)).rank with hρ
  obtain ⟨r, c, hdet⟩ := exists_det_submatrix_ne_zero (H.map (aeval γ)) hρ.symm
  set M : Matrix (Fin ρ) (Fin ρ) 𝕊[X] := H.submatrix r c with hM
  have hMγ : M.map (aeval γ) = (H.map (aeval γ)).submatrix r c := by
    rw [hM, Matrix.submatrix_map]
  have hMdet : M.det ≠ 0 := by
    intro h0
    apply hdet
    have h1 := AlgHom.map_det (aeval γ) M
    rw [AlgHom.mapMatrix_apply, hMγ, h0, map_zero] at h1
    exact h1.symm
  have hMdeg : M.det.natDegree ≤ ρ * Δ := by
    have := natDegree_det_le_of_natDegree_le M (Δ := Δ) fun i j => hdeg (r i) (c j)
    rwa [Fintype.card_fin] at this
  -- the ranks of the evaluated minors
  set b : 𝕊 → ℕ := fun s => (M.map (eval s)).rank with hb
  have hb_le : ∀ s, b s ≤ (H.map (eval s)).rank := by
    intro s
    have : M.map (eval s) = (H.map (eval s)).submatrix r c := by
      rw [hM, Matrix.submatrix_map]
    simp only [b]
    rw [this]
    exact Matrix.rank_submatrix_le _ _ _
  have hb_le' : ∀ s, b s ≤ ρ := fun s => by
    simpa using Matrix.rank_le_card_width (M.map (eval s))
  have hdvd : ∀ s : 𝕊, (X - C s) ^ (ρ - b s) ∣ M.det := fun s => by
    have := pow_X_sub_C_dvd_det M s
    rwa [Fintype.card_fin] at this
  have hcop : ((Finset.univ : Finset 𝕊) : Set 𝕊).Pairwise
      (Function.onFun IsCoprime fun s : 𝕊 => (X - C s) ^ (ρ - b s)) := by
    intro a _ a' _ haa'
    exact (Polynomial.pairwise_coprime_X_sub_C Function.injective_id haa').pow
  have hproddvd : (∏ s : 𝕊, (X - C s) ^ (ρ - b s)) ∣ M.det :=
    Finset.prod_dvd_of_coprime hcop fun s _ => hdvd s
  have hdegprod : (∏ s : 𝕊, (X - C s) ^ (ρ - b s)).natDegree = ∑ s : 𝕊, (ρ - b s) := by
    rw [Polynomial.natDegree_prod _ _ fun s _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero s)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hsum : ∑ s : 𝕊, (ρ - b s) ≤ ρ * Δ := by
    rw [← hdegprod]
    exact (Polynomial.natDegree_le_of_dvd hproddvd hMdet).trans hMdeg
  calc Fintype.card 𝕊 * ρ = ∑ _s : 𝕊, ρ := by simp
    _ = ∑ s : 𝕊, ((ρ - b s) + b s) := Finset.sum_congr rfl fun s _ => (Nat.sub_add_cancel (hb_le' s)).symm
    _ = ∑ s : 𝕊, (ρ - b s) + ∑ s : 𝕊, b s := Finset.sum_add_distrib
    _ ≤ ρ * Δ + ∑ s : 𝕊, (H.map (eval s)).rank :=
        Nat.add_le_add hsum (Finset.sum_le_sum fun s _ => hb_le s)
    _ = (∑ s : 𝕊, (H.map (eval s)).rank) + Δ * ρ := by ring

end LatticePrepro
