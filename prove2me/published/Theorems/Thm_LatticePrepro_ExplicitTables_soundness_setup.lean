import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_TableSoundness

open LatticePrepro
open Polynomial Matrix
open LatticePrepro.ExplicitTables
variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)
variable {FS m B}

theorem LatticePrepro.ExplicitTables.soundness_setup (hB : 2 ≤ B) (hm : 1 ≤ m)
    (hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (hw : 2 * hammingNorm y < B ^ m * Fintype.card FS.𝕊) :
    ∃ t : ℕ, t < B ^ m ∧ Fintype.card FS.𝕊 * t ≤ 2 * hammingNorm y ∧
      ∃ c : Fin (t + 1) → FS.K, c ≠ 0 ∧
        ∀ i : Fin (hLen p m B), ∑ j, c j * mom FS m B y (i.val + j.val) = 0 := by sorry
