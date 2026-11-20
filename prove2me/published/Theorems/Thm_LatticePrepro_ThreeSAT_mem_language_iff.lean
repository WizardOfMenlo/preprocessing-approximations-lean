import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT

open LatticePrepro
open LatticePrepro.ThreeSAT
variable {v : ℕ}

theorem LatticePrepro.ThreeSAT.mem_language_iff (x : Instance v) : encode x ∈ (circuit v).Language ↔ Satisfiable x := by sorry
