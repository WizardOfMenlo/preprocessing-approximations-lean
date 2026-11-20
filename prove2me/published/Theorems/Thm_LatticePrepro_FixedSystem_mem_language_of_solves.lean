import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

open LatticePrepro
open Finsupp
open LatticePrepro.FixedSystem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

theorem LatticePrepro.FixedSystem.mem_language_of_solves {x : Fin V.n → Bool} {v : Col V R → ZMod p}
    (hv : Solves V R ε x v) (hw : 2 * hammingNorm v < R.r * R.numBlocks) : x ∈ V.Language := by sorry
