import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

theorem LatticePrepro.LinearSystemFamily.code_no {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hx : L.IsNo g x) :
    ∀ c ∈ L.code, g * L.numBlocks < hammingDist (L.codeTarget x) c := by sorry
