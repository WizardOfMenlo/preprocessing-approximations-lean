import Mathlib

/-!
# Coefficient functions and moments

A *coefficient function* (Definition 4.1 of the paper) is a finitely supported function from a
field `Ω` to a coefficient ring `F` (in the paper, the prime field `𝔽_p`). We model it as a
`Finsupp` `Ω →₀ F`. Its `k`-th moment (Definition 4.2) is `∑ α, f α • α ^ k ∈ Ω`.

The main facts proved here are:
* `moment` is `F`-linear (`momentₗ`);
* the Vandermonde identification lemma (Lemma 4.3): a function supported on at most `t` points
  whose first `t` moments vanish is zero;
* the binomial identity for the moments of a translation difference (equation (20)).
-/

namespace LatticePrepro

open Finsupp

section Moment

variable {F Ω : Type*} [CommRing F] [CommRing Ω] [Algebra F Ω]

/-- The `k`-th moment `∑ α, f α • α ^ k` of a finitely supported `f : Ω →₀ F`
(Definition 4.2; with the convention `0 ^ 0 = 1`). -/
noncomputable def moment (f : Ω →₀ F) (k : ℕ) : Ω :=
  f.sum fun α c => c • α ^ k

@[simp] lemma moment_zero (k : ℕ) : moment (0 : Ω →₀ F) k = 0 := by
  simp [moment]

@[simp] lemma moment_single (α : Ω) (c : F) (k : ℕ) :
    moment (single α c) k = c • α ^ k := by
  simp [moment, sum_single_index]

end Moment

end LatticePrepro
