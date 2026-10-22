import LatticePrepro.Basic.Blocks

/-!
# Linear systems with a fixed matrix

A *linear system family* with a fixed matrix (cf. Section 2 of the paper) is a linear map
`A : (ι → F) →ₗ[F] W` together with a right-hand side `rhs x : W` for every instance `x`.
The columns `ι` are partitioned into blocks by `blk : ι → β`. The matrix `A` does not depend
on `x`; only `rhs x` does.

The *block-sparse linear-system problem with preprocessing* (Definition 3.6) asks to distinguish

* YES: `A v = rhs x` has a binary solution with at most one nonzero coordinate per block, from
* NO: every solution `v` of `A v = rhs x` has Hamming weight `> g · D`,

where `D = |β|` is the number of blocks and `g` the gap.
-/

namespace LatticePrepro

/-- A family of linear systems `A v = rhs x` with a fixed matrix and block-partitioned columns. -/
structure LinearSystemFamily (F : Type) [Field F] (X : Type) where
  /-- Column indices. -/
  ι : Type
  [fintypeι : Fintype ι]
  [decEqι : DecidableEq ι]
  /-- Block indices. -/
  β : Type
  [fintypeβ : Fintype β]
  [decEqβ : DecidableEq β]
  /-- The block partition of the columns. -/
  blk : ι → β
  /-- The block size. -/
  blockSize : ℕ
  card_fiber : ∀ s : β, (Finset.univ.filter fun i => blk i = s).card = blockSize
  /-- Codomain (rows). -/
  W : Type
  [addCommGroupW : AddCommGroup W]
  [moduleW : Module F W]
  /-- The fixed matrix. -/
  A : (ι → F) →ₗ[F] W
  /-- The right-hand side for instance `x`. -/
  rhs : X → W

namespace LinearSystemFamily

variable {F : Type} [Field F] {X : Type}

attribute [instance] fintypeι decEqι fintypeβ decEqβ addCommGroupW moduleW

variable (L : LinearSystemFamily F X)

/-- The number of blocks `D`. -/
abbrev numBlocks : ℕ := Fintype.card L.β

/-- Number of columns `n = D · b`. -/
lemma card_ι : Fintype.card L.ι = L.numBlocks * L.blockSize := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := L.blk) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp [L.card_fiber, Finset.sum_const, numBlocks]

/-- Solutions of the system for instance `x`. -/
def IsSolution (x : X) (v : L.ι → F) : Prop := L.A v = L.rhs x

/-- YES instances of BSLSP: a binary block-sparse solution exists. -/
def IsYes [DecidableEq F] (x : X) : Prop :=
  ∃ v : L.ι → F, L.IsSolution x v ∧ IsBinary v ∧ AtMostOnePerBlock L.blk v

/-- NO instances of BSLSP with gap `g`: every solution has weight more than `g · D`. -/
def IsNo [DecidableEq F] (g : ℕ) (x : X) : Prop :=
  ∀ v : L.ι → F, L.IsSolution x v → g * L.numBlocks < hammingNorm v

lemma isYes_weight_le [DecidableEq F] {x : X} (h : L.IsYes x) :
    ∃ v, L.IsSolution x v ∧ IsBinary v ∧ AtMostOnePerBlock L.blk v ∧
      hammingNorm v ≤ L.numBlocks := by
  obtain ⟨v, hv, hb, ho⟩ := h
  exact ⟨v, hv, hb, ho, hammingNorm_le_card_of_atMostOnePerBlock L.blk ho⟩

/-- A reduction with gap `g` from a language `Lang` to the BSLSP promise problem. -/
def IsGapReduction [DecidableEq F] (Lang : Set X) (g : ℕ) : Prop :=
  (∀ x ∈ Lang, L.IsYes x) ∧ (∀ x ∉ Lang, L.IsNo g x)

/-- Solutions form a coset of the kernel. -/
lemma isSolution_iff_sub_mem_ker {x : X} {v₀ v : L.ι → F} (h₀ : L.IsSolution x v₀) :
    L.IsSolution x v ↔ v - v₀ ∈ LinearMap.ker L.A := by
  simp only [IsSolution, LinearMap.mem_ker, map_sub] at *
  rw [h₀, sub_eq_zero]

end LinearSystemFamily

end LatticePrepro
