import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib

open LatticePrepro
open scoped ENNReal
open WithLp
open LatticePrepro.LatticeFamily
variable {X : Type} (Λ : LatticeFamily X)

theorem LatticePrepro.LatticeFamily.latticeDist_eq_infDist (pn : PNorm) (x : X) :
    Λ.latticeDist pn x =
      Metric.infDist (toLp pn.toENNReal (toReal (Λ.target x)) : PiLp pn.toENNReal fun _ => ℝ)
        (toLp pn.toENNReal '' (Λ.realLattice : Set (Λ.M → ℝ))) := by sorry
