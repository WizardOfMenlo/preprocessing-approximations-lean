import Mathlib

/-!
# Field setups for the explicit construction (Lemma A.3, existence part)

The explicit evaluation tables use a *sample field* `𝕊` of size `q = p^d` and an extension
`K = 𝕊(γ)` of degree `δ`, so that every element of `K` is a polynomial of degree `< δ` in `γ`
with coefficients in `𝕊`, and `1, γ, …, γ^{δ-1}` are `𝕊`-linearly independent.

We only need the *existence* of such fields (the paper's Lemma A.3 additionally constructs
them in polynomial time, which we do not formalize).
-/

namespace LatticePrepro

/-- A sample field `𝕊` of size `p^d` and an extension `K = 𝕊(γ)` of degree `δ`. -/
structure FieldSetup (p : ℕ) [Fact p.Prime] (d δ : ℕ) where
  /-- The sample field. -/
  𝕊 : Type
  [field𝕊 : Field 𝕊]
  [fintype𝕊 : Fintype 𝕊]
  [decEq𝕊 : DecidableEq 𝕊]
  [alg𝕊 : Algebra (ZMod p) 𝕊]
  card_𝕊 : Fintype.card 𝕊 = p ^ d
  /-- The moment field. -/
  K : Type
  [fieldK : Field K]
  [algK : Algebra (ZMod p) K]
  [alg𝕊K : Algebra 𝕊 K]
  [tower : IsScalarTower (ZMod p) 𝕊 K]
  /-- The generator `γ`. -/
  γ : K
  /-- Every element of `K` is a polynomial of degree `< δ` in `γ`. -/
  exists_aeval : ∀ x : K, ∃ f : Polynomial 𝕊, f.natDegree < δ ∧ Polynomial.aeval γ f = x
  /-- The powers `1, γ, …, γ^{δ-1}` are `𝕊`-linearly independent. -/
  linearIndependent_pow : LinearIndependent 𝕊 (fun i : Fin δ => γ ^ (i : ℕ))

namespace FieldSetup

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ}

attribute [instance] field𝕊 fintype𝕊 decEq𝕊 alg𝕊 fieldK algK alg𝕊K tower

variable (FS : FieldSetup p d δ)

end FieldSetup

end LatticePrepro
