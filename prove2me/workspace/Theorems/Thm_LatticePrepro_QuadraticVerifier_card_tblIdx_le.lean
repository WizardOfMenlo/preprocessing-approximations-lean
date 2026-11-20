import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

open LatticePrepro
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} (V : QuadraticVerifier p)

theorem LatticePrepro.QuadraticVerifier.card_tblIdx_le : Fintype.card V.TblIdx ≤ (V.S + 1) ^ 2 := by sorry
