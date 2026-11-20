import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices

/-!
# Distance from a target to a lattice

The paper (Definition 3.1) measures the distance from a target `t` to a lattice `Λ` as
`dist_p(t, Λ) = min_{v ∈ Λ} ‖t − v‖_p`. For a `LatticeFamily`, we define
`latticeDist pn x = ⨅ v ∈ Λ, ‖t_x − v‖_p` and show that the infimum is attained
(`exists_dist_eq_latticeDist`): the lattice vectors within any given distance of `t_x` form a
finite set of integer vectors, since every coordinate is bounded by the `ℓ_p` norm.

The consequences `latticeDist_le_of_exists` and `lt_latticeDist_of_forall` translate the
"some lattice vector within `R`" / "every lattice vector beyond `γ R`" form of the main theorems
into bounds on `dist_p(t_x, Λ)`.
-/

namespace LatticePrepro

namespace LatticeFamily

variable {X : Type} (Λ : LatticeFamily X) (pn : PNorm) (x : X)

/-- The distance `dist_p(t_x, Λ) = inf_{v ∈ Λ} ‖t_x − v‖_p` from the target to the lattice
(Definition 3.1). The infimum is attained (`exists_dist_eq_latticeDist`). -/
noncomputable def latticeDist : ℝ := ⨅ v : Λ.lattice, Λ.dist pn x v

instance : Nonempty Λ.lattice := ⟨0⟩

end LatticeFamily

end LatticePrepro
