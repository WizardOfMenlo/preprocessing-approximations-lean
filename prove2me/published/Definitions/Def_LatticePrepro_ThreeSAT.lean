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

/-!
# Theorem 5.1 for 3SAT

The main theorems of `Main.lean` are stated for an arbitrary quadratic verifier. Instantiating
them with the verifier circuit of `Verifier/ThreeSAT.lean` (Claim 3.15 and Definition 3.14 turn
it into a quadratic verifier with the same language) gives the paper's Theorem 5.1 for 3SAT:
fixed codes and lattices of dimension `M ≤ n^C`, where `n = (2v)^3` is the instance length of
3SAT on `v` variables, with targets `t_x` such that satisfiable instances have
`dist(t_x, ·) ≤ R` and unsatisfiable ones `dist(t_x, ·) > M^{1/s - ε} · R`.
-/

namespace LatticePrepro

namespace ThreeSAT

/-- The language of satisfiable 3SAT instances on `v` variables. -/
def SAT (v : ℕ) : Set (Instance v) := {x | Satisfiable x}

end ThreeSAT

end LatticePrepro
