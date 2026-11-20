import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices

open LatticePrepro

theorem LatticePrepro.radius_bound_gt_two {q t D A B w : ℝ} (hq : 2 < q) (ht : 1 ≤ t) (hD : 1 ≤ D)
    (hB : 0 ≤ B) (hw : w ≤ A / t) (hAB : A ≤ (2 * (t * D)) ^ (1 - 2 / q) * B ^ (2 / q)) :
    w ≤ 16 * D * (B ^ (1 / q) / (⌈(t * D) ^ (1 / q)⌉₊ : ℝ)) ^ (2 : ℝ) := by sorry
