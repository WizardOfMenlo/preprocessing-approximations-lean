import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Main
import Theorems.Thm_LatticePrepro_code_gap

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

/-- **Theorem 5.1 for codes**, paper form: for every finite field `F` of characteristic `p` and
every `0 < ε < 1`, there is a constant `C` such that every quadratic verifier `V` over `𝔽_p`
admits a fixed code of block length `M ≤ (S + 1)^C` with targets `t_x` and an integer radius
`R ≥ 1` such that `x ∈ L(V)` implies `dist(t_x, 𝒞) ≤ R` and `x ∉ L(V)` implies
`dist(t_x, 𝒞) > M^{1 - ε} · R`. -/
private theorem exists_code_gap (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℕ, ∀ V : QuadraticVerifier p, Nonempty (CodeGap F ε V.Language (V.S + 1) C) :=
  ⟨_, code_gap p F ε hε hε1⟩

end LatticePrepro

open LatticePrepro
theorem solution (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℕ, ∀ V : QuadraticVerifier p, Nonempty (CodeGap F ε V.Language (V.S + 1) C) :=
  @LatticePrepro.exists_code_gap p _ F _ _ _ _ ε hε hε1
