import LatticePrepro.Basic.Matrix

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
