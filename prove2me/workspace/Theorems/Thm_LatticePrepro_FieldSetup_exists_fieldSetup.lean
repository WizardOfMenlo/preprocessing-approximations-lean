import Mathlib
import Definitions.Def_LatticePrepro_Tables_FieldSetup

open LatticePrepro
open LatticePrepro.FieldSetup
variable {p : ℕ} [Fact p.Prime] {d δ : ℕ}

theorem LatticePrepro.FieldSetup.exists_fieldSetup (p : ℕ) [Fact p.Prime] (d δ : ℕ) (hd : 1 ≤ d) (hδ : 1 ≤ δ) :
    Nonempty (FieldSetup p d δ) := by sorry
