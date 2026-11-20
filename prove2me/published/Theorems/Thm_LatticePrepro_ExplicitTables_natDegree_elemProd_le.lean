import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable

open LatticePrepro
open Polynomial
open LatticePrepro.ExplicitTables
variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)
variable {FS m B}

theorem LatticePrepro.ExplicitTables.natDegree_elemProd_le (α : FS.K) {η : Fin m → ℕ} (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    (elemProd FS m B α η).natDegree ≤ degBound p m B δ := by sorry
