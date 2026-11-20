import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic

/-!
# Moment representations (Definition 4.4)

A *moment representation* over a field `K` of characteristic `p` consists of evaluation tables
`y : ι → 𝔽_p` (with coordinates partitioned into blocks of equal size), linear *evaluation table
constraints* `constraint y = 0`, and `𝔽_p`-linear *moment maps* `momentMap k : (ι → 𝔽_p) →ₗ K`
for the orders `k : Fin (2r - 1)`, i.e. `0 ≤ k ≤ 2r - 2`, such that

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
  /-- The moment maps `M̂_k` for the orders `0 ≤ k ≤ 2r - 2`. -/
  momentMap : Fin (2 * r - 1) → (ι → ZMod p) →ₗ[ZMod p] K
  /-- Completeness: every field element has a block-unit table. -/
  complete : ∀ α : K, ∃ y : ι → ZMod p, IsBinary y ∧ ExactlyOnePerBlock blk y ∧
    constraint y = 0 ∧ ∀ k, momentMap k y = α ^ (k : ℕ)
  /-- Soundness: light tables represent sparse coefficient functions over `Ω`. -/
  sound : ∀ y : ι → ZMod p, constraint y = 0 → 2 * hammingNorm y < r * Fintype.card β →
    ∃ f : Ω →₀ ZMod p, (∀ k, algebraMap K Ω (momentMap k y) = moment f k) ∧
      Fintype.card β * f.support.card ≤ 2 * hammingNorm y

namespace MomentRepresentation

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]

attribute [instance] fintypeι decEqι fintypeβ decEqβ addCommGroupW moduleW

variable (R : MomentRepresentation p K Ω)

/-- The number of blocks `D`. -/
abbrev numBlocks : ℕ := Fintype.card R.β

/-! ### Moment orders -/

/-- The moment orders `0 ≤ k ≤ 2r - 2` carried by the representation. -/
abbrev Order : Type := Fin (2 * R.r - 1)

/-- An order `k < r` as a moment order (`r ≤ 2r - 2`). -/
def low (k : Fin R.r) : R.Order := ⟨k, by have := R.two_le_r; have := k.isLt; omega⟩

@[simp] lemma low_val (k : Fin R.r) : (R.low k : ℕ) = k := rfl

/-- The order `k + 1` for `k < r`, as a moment order (`k + 1 ≤ r ≤ 2r - 2`). -/
def lowSucc (k : Fin R.r) : R.Order := ⟨k + 1, by have := R.two_le_r; have := k.isLt; omega⟩

@[simp] lemma lowSucc_val (k : Fin R.r) : (R.lowSucc k : ℕ) = k + 1 := rfl

/-- The orders below a moment order `k`, as moment orders. -/
def below (k : R.Order) (j : Fin k) : R.Order := Fin.castLE k.isLt.le j

@[simp] lemma below_val (k : R.Order) (j : Fin k) : (R.below k j : ℕ) = j := rfl

end MomentRepresentation

end LatticePrepro
