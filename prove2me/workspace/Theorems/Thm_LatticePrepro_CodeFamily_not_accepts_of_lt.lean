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
open LatticePrepro.CodeFamily
variable {F : Type} [Field F] [DecidableEq F] {X : Type} (C : CodeFamily F X)

theorem LatticePrepro.CodeFamily.not_accepts_of_lt {g R : ℕ} {x : X} (hx : g * R < codeDist (C.target x) C.code)
    (c : C.M → F) : ¬ C.Accepts g R x c := by sorry
