import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_Codes_Ext
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_ConstructionA_Ext
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Hadamard_Ext
import Definitions.Def_LatticePrepro_Conversions_Padding
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Conversions_Lattices_Ext
import Definitions.Def_LatticePrepro_Lattices_Distance
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
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Main
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT_Ext
import Definitions.Def_LatticePrepro_Explicit

open LatticePrepro
open LatticePrepro.ThreeSAT
open QuadraticVerifier

theorem LatticePrepro.ThreeSAT.explicit_lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier 2 v).Tables (1 - pn.s * ε),
      ((T.latticeFamily pn).comap encode).HasGap pn (T.latticeRadius pn) ε (SAT v) (len v) C := by sorry
