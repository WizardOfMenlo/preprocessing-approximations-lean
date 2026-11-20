import Mathlib

open Polynomial Matrix

theorem LatticePrepro.card_mul_rank_eval_le {𝕊 : Type*} [Field 𝕊] [Fintype 𝕊] [DecidableEq 𝕊]
    {K : Type*} [Field K] [Algebra 𝕊 K] (γ : K) {ℓ Δ : ℕ}
    (H : Matrix (Fin ℓ) (Fin ℓ) 𝕊[X]) (hdeg : ∀ i j, (H i j).natDegree ≤ Δ) :
    Fintype.card 𝕊 * (H.map (aeval γ)).rank ≤
      (∑ s : 𝕊, (H.map (eval s)).rank) + Δ * (H.map (aeval γ)).rank := by sorry
