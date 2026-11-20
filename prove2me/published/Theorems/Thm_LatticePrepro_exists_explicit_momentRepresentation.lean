import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit

open LatticePrepro
open Polynomial
open ExplicitTables

theorem LatticePrepro.exists_explicit_momentRepresentation (p : ℕ) [Fact p.Prime] (S m B : ℕ)
    (hS : 2 ≤ S) (hm : 1 ≤ m) (hB : 2 ≤ B) : Nonempty (ExplicitMomentRepresentation p S m B) := by sorry
