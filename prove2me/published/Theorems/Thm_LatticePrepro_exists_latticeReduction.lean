import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices

open LatticePrepro

theorem LatticePrepro.exists_latticeReduction {p : ℕ} [Fact p.Prime] {X : Type}
    (L : LinearSystemFamily (ZMod p) X) {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    (pn : PNorm) : Nonempty (LatticeReduction L g pn) := by sorry
