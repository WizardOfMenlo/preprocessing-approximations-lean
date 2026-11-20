import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {X : Type} (F : Type) [Field F] [Algebra (ZMod p) F]

theorem LatticePrepro.CodeFamily.codeDist_extend [DecidableEq F] (C : CodeFamily (ZMod p) X) (x : X) :
    CodeFamily.codeDist ((C.extend F).target x) (C.extend F).code =
      CodeFamily.codeDist (C.target x) C.code := by sorry
