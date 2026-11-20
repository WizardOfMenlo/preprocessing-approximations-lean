import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier
import Definitions.Def_LatticePrepro_PCP_Code

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}

theorem LatticePrepro.ObliviousPCP.codeDist_le_of_mem {Lang : Set X} (hc : P.PerfectlyComplete Lang)
    (E : (P.Views → F) →ₗ[F] (Fin B → F)) (g : ℕ) {x : X} (hx : x ∈ Lang) :
    CodeFamily.codeDist (P.target E g x) (P.code E g) ≤ P.radius B := by sorry
