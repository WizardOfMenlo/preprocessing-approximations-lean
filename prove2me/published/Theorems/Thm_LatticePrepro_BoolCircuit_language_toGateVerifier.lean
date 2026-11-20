import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit

open LatticePrepro
open LatticePrepro.BoolCircuit
variable (C : BoolCircuit)

theorem LatticePrepro.BoolCircuit.language_toGateVerifier : C.toGateVerifier.Language = C.Language := by sorry
