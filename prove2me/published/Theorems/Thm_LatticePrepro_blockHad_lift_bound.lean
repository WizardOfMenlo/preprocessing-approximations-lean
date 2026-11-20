import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices

open LatticePrepro
open Finset
variable {p : ℕ} [Fact p.Prime] {β : Type*} [Fintype β] [DecidableEq β] {k : ℕ}

theorem LatticePrepro.blockHad_lift_bound {e : β × Hadamard.Idx k → ZMod p} (hb : IsBinary e)
    (h1 : AtMostOnePerBlock Prod.fst e) :
    (∀ su, |Hadamard.blockHad k (liftZMod e) su| ≤ 1) ∧
    (univ.filter fun su => Hadamard.blockHad k (liftZMod e) su ≠ 0).card ≤
      hammingNorm e * 2 ^ k := by sorry
