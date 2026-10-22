import LatticePrepro.Basic.Blocks
import LatticePrepro.Moments.Basic

/-!
# Moment representations (Definition 4.4)

A *moment representation* over a field `K` of characteristic `p` consists of evaluation tables
`y : ι → 𝔽_p` (with coordinates partitioned into blocks of equal size), linear *evaluation table
constraints* `constraint y = 0`, and `𝔽_p`-linear *moment maps* `momentMap k : (ι → 𝔽_p) →ₗ K`
for `0 ≤ k ≤ 2r - 2`, such that

* **completeness**: every `α : K` has a binary table with exactly one `1` per block, satisfying
  the constraints, whose moments are `α ^ k`;
* **soundness**: every table satisfying the constraints with weight below the threshold
  `r · D / 2` (where `D` is the number of blocks) represents a coefficient function
  `f : Ω →₀ 𝔽_p` on an extension field `Ω` of `K`, with `|supp f| ≤ 2 · wt(y) / D`.

We fix a single extension field `Ω` of `K` once and for all (in the explicit construction,
an algebraic closure); this avoids embedding several finite extensions into a common one.
-/

namespace LatticePrepro

/-- A moment representation over `K` (Definition 4.4), with represented coefficient functions
living on the extension field `Ω`. -/
structure MomentRepresentation (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K]
    (Ω : Type) [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω] where
  /-- The moment parameter `r`. -/
  r : ℕ
  two_le_r : 2 ≤ r
  /-- Coordinates of an evaluation table. -/
  ι : Type
  [fintypeι : Fintype ι]
  [decEqι : DecidableEq ι]
  /-- Blocks. -/
  β : Type
  [fintypeβ : Fintype β]
  [decEqβ : DecidableEq β]
  /-- The partition of the coordinates into blocks. -/
  blk : ι → β
  /-- The block size. -/
  blockSize : ℕ
  card_fiber : ∀ s : β, (Finset.univ.filter fun i => blk i = s).card = blockSize
  /-- Codomain of the evaluation table constraints. -/
  W : Type
  [addCommGroupW : AddCommGroup W]
  [moduleW : Module (ZMod p) W]
  /-- The evaluation table constraints `constraint y = 0`. -/
  constraint : (ι → ZMod p) →ₗ[ZMod p] W
  /-- The moment maps `M̂_k`. Only orders `k ≤ 2r - 2` matter. -/
  momentMap : ℕ → (ι → ZMod p) →ₗ[ZMod p] K
  /-- Completeness: every field element has a block-unit table. -/
  complete : ∀ α : K, ∃ y : ι → ZMod p, IsBinary y ∧ ExactlyOnePerBlock blk y ∧
    constraint y = 0 ∧ ∀ k ≤ 2 * r - 2, momentMap k y = α ^ k
  /-- Soundness: light tables represent sparse coefficient functions over `Ω`. -/
  sound : ∀ y : ι → ZMod p, constraint y = 0 → 2 * hammingNorm y < r * Fintype.card β →
    ∃ f : Ω →₀ ZMod p, (∀ k ≤ 2 * r - 2, algebraMap K Ω (momentMap k y) = moment f k) ∧
      Fintype.card β * f.support.card ≤ 2 * hammingNorm y

namespace MomentRepresentation

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]

attribute [instance] fintypeι decEqι fintypeβ decEqβ addCommGroupW moduleW

variable (R : MomentRepresentation p K Ω)

/-- The number of blocks `D`. -/
abbrev numBlocks : ℕ := Fintype.card R.β

/-- The evaluation table length `D · b`. -/
lemma card_ι : Fintype.card R.ι = R.numBlocks * R.blockSize := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := R.blk) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp [R.card_fiber, Finset.sum_const, numBlocks]

/-- A table representing a coefficient function `f`: its moments of order `≤ 2r - 2`
agree with those of `f`. -/
def Represents (y : R.ι → ZMod p) (f : Ω →₀ ZMod p) : Prop :=
  ∀ k ≤ 2 * R.r - 2, algebraMap K Ω (R.momentMap k y) = moment f k

/-- A chosen block-unit table for `α` (Completeness). -/
noncomputable def elemTable (α : K) : R.ι → ZMod p := (R.complete α).choose

lemma elemTable_binary (α : K) : IsBinary (R.elemTable α) := (R.complete α).choose_spec.1

lemma elemTable_onePerBlock (α : K) : ExactlyOnePerBlock R.blk (R.elemTable α) :=
  (R.complete α).choose_spec.2.1

lemma constraint_elemTable (α : K) : R.constraint (R.elemTable α) = 0 :=
  (R.complete α).choose_spec.2.2.1

lemma momentMap_elemTable (α : K) {k : ℕ} (hk : k ≤ 2 * R.r - 2) :
    R.momentMap k (R.elemTable α) = α ^ k :=
  (R.complete α).choose_spec.2.2.2 k hk

lemma hammingNorm_elemTable_le (α : K) : hammingNorm (R.elemTable α) ≤ R.numBlocks :=
  hammingNorm_le_card_of_atMostOnePerBlock R.blk (R.elemTable_onePerBlock α).atMostOne

/-- A moment representation has at least one block (otherwise no table could have zeroth
moment `1`). -/
lemma numBlocks_pos : 0 < R.numBlocks := by
  by_contra h
  have hβ : Fintype.card R.β = 0 := by simpa [numBlocks] using h
  have hι : Fintype.card R.ι = 0 := by rw [R.card_ι, numBlocks, hβ, zero_mul]
  have hy : R.elemTable 1 = 0 := by
    funext i
    exact absurd (Fintype.card_pos_iff.mpr ⟨i⟩) (by omega)
  have h0 := R.momentMap_elemTable 1 (k := 0) (Nat.zero_le _)
  rw [hy, map_zero, pow_zero] at h0
  exact zero_ne_one h0

lemma card_ι_pos_iff : 0 < Fintype.card R.ι ↔ 0 < R.blockSize := by
  rw [R.card_ι]
  constructor
  · intro h; exact Nat.pos_of_mul_pos_left h
  · intro h; exact Nat.mul_pos R.numBlocks_pos h

end MomentRepresentation

end LatticePrepro
