import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness

/-!
# Explicit moment representations (Construction A.4, Theorem A.8)

For a prime `p` and integers `S ≥ 2`, `m ≥ 1`, `B ≥ 2`, we construct a finite field `K` of
characteristic `p`, an encoding tuple `ε` of length `S` over `K`, and a moment representation
over `K` with

* moment parameter `r = B^m`,
* `D = q` blocks of size `b = q^m`, where `q` is a power of `p` with
  `B ≤ q < 8 · p^3 · m · S · B`.

As in Construction A.4, `K = 𝕊(γ)` has degree `δ` over the sample field `𝕊` of size `q`, where
`δ` is the least power of `p` with `δ ≥ S` and `q` is the least power of `p` with
`q ≥ 8 p m B δ`. The represented coefficient functions live on an algebraic closure `Ω` of `K`.
The output is bundled as an `ExplicitMomentRepresentation`.

The ingredients are the construction (`Tables/Construction.lean`), completeness through the
element tables (`Tables/ElementTable.lean`), the rank analysis of the polynomial matrix
(`Tables/TableSoundness.lean`), and the Hankel reconstruction theorem (`Tables/Hankel.lean`).
-/

namespace LatticePrepro

open Polynomial

/-- The output of Theorem A.8: a field `K` of characteristic `p`, an encoding tuple of length `S`
over `K`, and a moment representation over `K` with `r = B^m` and `q` blocks of size `q^m`, where
`q` is a power of `p` with `B ≤ q < 8 p^3 m S B`. -/
structure ExplicitMomentRepresentation (p : ℕ) [Fact p.Prime] (S m B : ℕ) where
  /-- The moment field. -/
  K : Type
  [fieldK : Field K]
  [algK : Algebra (ZMod p) K]
  /-- The encoding tuple `(0, 1, γ, …, γ^{S-1})`. -/
  ε : EncodingTuple p K S
  /-- The moment representation; coefficient functions live on an algebraic closure of `K`. -/
  R : MomentRepresentation p K (AlgebraicClosure K)
  /-- The sample field size `q`, which is the number of blocks. -/
  q : ℕ
  r_eq : R.r = B ^ m
  numBlocks_eq : R.numBlocks = q
  blockSize_eq : R.blockSize = q ^ m
  q_eq_pow : ∃ d : ℕ, 1 ≤ d ∧ q = p ^ d
  le_q : B ≤ q
  q_lt : q < 8 * p ^ 3 * m * S * B

attribute [instance] ExplicitMomentRepresentation.fieldK ExplicitMomentRepresentation.algK

end LatticePrepro
