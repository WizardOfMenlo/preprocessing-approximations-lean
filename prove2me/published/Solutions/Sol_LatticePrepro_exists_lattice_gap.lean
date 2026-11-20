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
import Theorems.Thm_LatticePrepro_lattice_gap

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

/-- **Theorem 5.1 for lattices**, paper form: for every norm exponent `1 ≤ p ≤ ∞` with
`s = min {p, 2}` and every `0 < ε < 1/s`, there is a constant `C` such that every quadratic
verifier `V` over `𝔽_2` admits a fixed full-rank lattice `Λ ⊆ ℤ^M` with `M ≤ (S + 1)^C`, integer
targets `t_x` and an integer radius `R ≥ 1` such that `x ∈ L(V)` implies `dist_p(t_x, Λ) ≤ R`
and `x ∉ L(V)` implies `dist_p(t_x, Λ) > M^{1/s - ε} · R`. -/
private theorem exists_lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ V : QuadraticVerifier 2, Nonempty (LatticeGap pn ε V.Language (V.S + 1) C) :=
  ⟨_, lattice_gap pn ε hε hε1⟩

end LatticePrepro

open LatticePrepro
theorem solution (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ V : QuadraticVerifier 2, Nonempty (LatticeGap pn ε V.Language (V.S + 1) C) :=
  @LatticePrepro.exists_lattice_gap pn ε hε hε1
