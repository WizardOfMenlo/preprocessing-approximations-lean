import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Conversions_SearchTest

open LatticePrepro
open LatticePrepro.LatticeReduction
variable {p : ℕ} [Fact p.Prime] {X : Type} {L : LinearSystemFamily (ZMod p) X} {g : ℕ}
  {pn : PNorm} (Red : LatticeReduction L g pn)

theorem LatticePrepro.LatticeReduction.accepts_of_isApprox {f : ℝ} (hf : 0 ≤ f) (hgf : 16 * f ^ pn.s ≤ g) {x : X}
    (hx : L.IsYes x) {v : Red.Λ.M → ℤ} (hv : Red.IsApprox f x v) : Red.Accepts x v := by sorry
