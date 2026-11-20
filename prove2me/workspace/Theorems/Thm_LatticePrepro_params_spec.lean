import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Main

open LatticePrepro

theorem LatticePrepro.params_spec (p : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (S n : ℕ) (hS : 1 ≤ S)
    (hn : 1 ≤ n)
    (hbound : n ^ momentAxes δ ≤ (8 * p ^ 4 * momentAxes δ * (S + 1)) ^
      ((momentAxes δ + 7) * momentAxes δ) * ((S + 1) ^ gapExp p δ) ^ (momentAxes δ + 1)) :
    64 * (n : ℝ) ^ δ ≤ ((S + 1) ^ gapExp p δ : ℕ) ∧ 4 * n ≤ (S + 1) ^ sizeExp p δ := by sorry
