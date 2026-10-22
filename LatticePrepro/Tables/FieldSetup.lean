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

/-- Field setups exist for every `d ≥ 1` and `δ ≥ 1` (take `𝕊 = 𝔽_{p^d}` and
`K = 𝔽_{p^{dδ}}`, with `γ` a primitive element of `K/𝕊`). -/
theorem exists_fieldSetup (p : ℕ) [Fact p.Prime] (d δ : ℕ) (hd : 1 ≤ d) (hδ : 1 ≤ δ) :
    Nonempty (FieldSetup p d δ) := by
  classical
  have hd0 : d ≠ 0 := by omega
  have hdδ : d * δ ≠ 0 := Nat.mul_ne_zero hd0 (by omega)
  let 𝕊 := GaloisField p d
  let K := GaloisField p (d * δ)
  letI : Fintype 𝕊 := Fintype.ofFinite _
  letI : Fintype K := Fintype.ofFinite _
  -- the embedding `𝕊 → K`
  obtain ⟨φ⟩ : Nonempty (𝕊 →ₐ[ZMod p] K) := by
    apply FiniteField.nonempty_algHom_of_finrank_dvd
    rw [GaloisField.finrank p hd0, GaloisField.finrank p hdδ]
    exact Dvd.intro δ rfl
  letI : Algebra 𝕊 K := φ.toRingHom.toAlgebra
  have : IsScalarTower (ZMod p) 𝕊 K :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  -- cardinalities and the degree `[K : 𝕊] = δ`
  have hcard𝕊 : Fintype.card 𝕊 = p ^ d := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p d hd0
  have hcardK : Fintype.card K = p ^ (d * δ) := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p (d * δ) hdδ
  have hfin : Module.finrank 𝕊 K = δ := by
    have h := Module.card_eq_pow_finrank (K := 𝕊) (V := K)
    rw [hcardK, hcard𝕊, ← pow_mul] at h
    have h2 := Nat.pow_right_injective (Fact.out : p.Prime).two_le h
    exact (Nat.eq_of_mul_eq_mul_left (by omega) h2).symm
  -- a power basis of `K` over `𝕊`
  let pb : PowerBasis 𝕊 K := Field.powerBasisOfFiniteOfSeparable 𝕊 K
  have hdim : pb.dim = δ := by rw [← pb.finrank, hfin]
  have hli : LinearIndependent 𝕊 (fun i : Fin δ => pb.gen ^ (i : ℕ)) := by
    have h := pb.basis.linearIndependent
    rw [pb.coe_basis] at h
    exact h.comp (finCongr hdim.symm) (finCongr hdim.symm).injective
  refine ⟨{ 𝕊 := 𝕊, card_𝕊 := hcard𝕊, K := K, γ := pb.gen, exists_aeval := ?_,
            linearIndependent_pow := hli }⟩
  intro x
  obtain ⟨f, hf, hx⟩ := pb.exists_eq_aeval x
  exact ⟨f, hdim ▸ hf, hx.symm⟩

variable (FS : FieldSetup p d δ)

/-- The powers of `γ` are `𝔽_p`-linearly independent as well. -/
lemma linearIndependent_pow_zmod :
    LinearIndependent (ZMod p) (fun i : Fin δ => FS.γ ^ (i : ℕ)) :=
  FS.linearIndependent_pow.restrict_scalars (by
    intro a b hab
    simpa using (algebraMap (ZMod p) FS.𝕊).injective (by simpa [Algebra.smul_def] using hab))

end FieldSetup

end LatticePrepro
