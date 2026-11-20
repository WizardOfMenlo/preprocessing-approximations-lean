import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates

open LatticePrepro
open LatticePrepro.GateVerifier
variable (W : GateVerifier)
variable (p : ℕ)
variable [Fact p.Prime]

theorem LatticePrepro.GateVerifier.language_toQuadratic : (W.toQuadratic p).Language = W.Language := by sorry
