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
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit
import Definitions.Def_LatticePrepro_Verifier_Expr
import Definitions.Def_LatticePrepro_Verifier_ThreeSAT
import Definitions.Def_LatticePrepro_ThreeSAT

open LatticePrepro
open LatticePrepro.ThreeSAT

theorem LatticePrepro.ThreeSAT.fixed_code_and_lattice_gaps :
    (∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [DecidableEq F]
        [Algebra (ZMod p) F] (ε : ℝ), 0 < ε → ε < 1 →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (CodeGap F ε (SAT v) (len v) C)) ∧
      (∀ (pn : PNorm) (ε : ℝ), 0 < ε → ε < 1 / pn.s →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (LatticeGap pn ε (SAT v) (len v) C)) := by sorry
