import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard

/-!
# From codes to lattices (Lemma 3.12, Appendix B.2–B.3)

* `ℓ_p` norms on `M → ℝ` for `1 ≤ p < ∞` and `p = ∞` (`PNorm`).
* Construction A: `Λ_𝒞 = {v ∈ ℤ^M : v mod p ∈ 𝒞}` (Lemma B.1).
* The block Hadamard map (Lemma B.2): for `2 ≤ p ≤ ∞`, multiply lattice and target by a
  block-diagonal matrix of Sylvester–Hadamard matrices.
* The lattice reduction (Lemma 3.12, `LatticeReduction`, `exists_latticeReduction`): a fixed
  lattice `Λ`, an integer radius `R`, targets `t_x` and a residual weight such that YES instances
  have a lattice vector within distance `R` and NO instances have every lattice vector at distance
  more than `(g / 16)^{1/s} · R`, where `s = min {p, 2}`.
-/

namespace LatticePrepro

/-- A norm exponent: a real `p ≥ 1`, or `∞`. -/
inductive PNorm
  | fin (p : ℝ) (hp : 1 ≤ p)
  | inf

namespace PNorm

/-- The `ℓ_p` norm of a real vector. -/
noncomputable def norm {M : Type} [Fintype M] : PNorm → (M → ℝ) → ℝ
  | fin p _ => fun v => (∑ i, |v i| ^ p) ^ (1 / p)
  | inf => fun v => ⨆ i, |v i|

/-- The exponent `s = min {p, 2}` (`s = 2` for `p = ∞`). -/
noncomputable def s : PNorm → ℝ
  | fin p _ => min p 2
  | inf => 2

end PNorm

/-- A fixed lattice `Λ ⊆ ℤ^M` with an integer target for every instance. -/
structure LatticeFamily (X : Type) where
  /-- Coordinates. -/
  M : Type
  [fintypeM : Fintype M]
  [decEqM : DecidableEq M]
  /-- The lattice, as a `ℤ`-submodule of `ℤ^M`. -/
  lattice : Submodule ℤ (M → ℤ)
  /-- The target for instance `x`. -/
  target : X → (M → ℤ)

namespace LatticeFamily

attribute [instance] fintypeM decEqM

variable {X : Type} (Λ : LatticeFamily X)

/-- The real vector of an integer vector. -/
def toReal {M : Type} (v : M → ℤ) : M → ℝ := fun i => (v i : ℝ)

/-- Distance in `ℓ_p` from the target to a lattice vector. -/
noncomputable def dist (pn : PNorm) (x : X) (v : Λ.M → ℤ) : ℝ :=
  pn.norm (toReal (Λ.target x - v))

end LatticeFamily

/-! ### Padding the code to blocks of size a power of two -/

/-! ### Block-sparse binary vectors under the Hadamard map -/

/-! ### Real-number bounds for the radius -/

/-! ### The lattice reduction: statement -/

/-- The output of Lemma 3.12 for a linear system family `L`, a gap `g` and a norm exponent `pn`:
a fixed lattice `Λ ⊆ ℤ^M` with `2 n ≤ M < 4 n` (`n = |ι|`), containing `N · ℤ^M` for some
`N > 0` (full rank), an integer radius `1 ≤ R ≤ M`, and a *residual weight* `w = weight x v`
computable from a lattice vector `v`, such that

* YES instances have a lattice vector within `ℓ_p`-distance `R` of the target;
* `w ≤ 16 · D · (dist / R)^s` for every lattice vector, and `w > g · D` on NO instances.

The residual weight is the quantity tested in Lemma 5.2 (`Conversions/SearchTest.lean`). -/
structure LatticeReduction {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)
    (g : ℕ) (pn : PNorm) where
  /-- The fixed lattice and the targets. -/
  Λ : LatticeFamily X
  /-- The radius. -/
  R : ℕ
  one_le_R : 1 ≤ R
  R_le_card : R ≤ Fintype.card Λ.M
  two_mul_card_le : 2 * Fintype.card L.ι ≤ Fintype.card Λ.M
  card_lt_four_mul : Fintype.card Λ.M < 4 * Fintype.card L.ι
  /-- The lattice contains `N · ℤ^M`. -/
  N : ℕ
  N_pos : 0 < N
  smul_mem : ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice
  /-- The residual weight of a lattice vector. -/
  weight : X → (Λ.M → ℤ) → ℕ
  yes : ∀ x, L.IsYes x → ∃ v ∈ Λ.lattice, Λ.dist pn x v ≤ R
  weight_le : ∀ x, ∀ v ∈ Λ.lattice,
    (weight x v : ℝ) ≤ 16 * L.numBlocks * (Λ.dist pn x v / R) ^ pn.s
  lt_weight : ∀ x, L.IsNo g x → ∀ v ∈ Λ.lattice, g * L.numBlocks < weight x v

/-! ### The three cases of the lattice reduction -/

end LatticePrepro
