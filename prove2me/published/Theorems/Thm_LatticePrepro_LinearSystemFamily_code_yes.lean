import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

theorem LatticePrepro.LinearSystemFamily.code_yes {x : X} (hx : L.IsYes x) :
    ∃ e : L.ι ⊕ L.ι → ZMod p, IsBinary e ∧ AtMostOnePerBlock L.codeBlk e ∧
      hammingNorm e ≤ L.numBlocks ∧ L.codeTarget x - e ∈ L.code := by sorry
