import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance

/-!
# Bridge to Mathlib's `PiLp` norms and `IsZLattice`

The lattice statements of the main theorems are phrased with our own `PNorm.norm` and with
`LatticeFamily.lattice : Submodule ℤ (M → ℤ)`. This file identifies them with Mathlib's notions:

* `PNorm.norm v = ‖toLp p v‖` for the `L^p` norm on `PiLp p (fun _ : M => ℝ)`
  (`PNorm.norm_eq_piLp`), and `LatticeFamily.dist` is the `PiLp` distance
  (`LatticeFamily.dist_eq_piLp`);
* `LatticeFamily.latticeDist` is `Metric.infDist` from the target to the real image of the lattice
  (`LatticeFamily.latticeDist_eq_infDist`);
* the real image `LatticeFamily.realLattice ⊆ ℝ^M` of the lattice is discrete, and it is an
  `IsZLattice` (a discrete subgroup spanning `ℝ^M`) whenever it contains `N · ℤ^M` for some `N > 0`
  (`LatticeFamily.isZLattice_realLattice`), which is the full-rank condition of Lemma 3.12.
-/

namespace LatticePrepro

open scoped ENNReal

open WithLp

/-! ### Norm exponents as elements of `ℝ≥0∞` -/

namespace PNorm

/-- The norm exponent as an element of `ℝ≥0∞` (`p ↦ p`, `∞ ↦ ⊤`). -/
noncomputable def toENNReal : PNorm → ℝ≥0∞
  | fin p _ => ENNReal.ofReal p
  | inf => ⊤

lemma one_le_toENNReal (pn : PNorm) : 1 ≤ pn.toENNReal := by
  cases pn with
  | fin p hp =>
    show 1 ≤ ENNReal.ofReal p
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  | inf => exact le_top

instance (pn : PNorm) : Fact (1 ≤ pn.toENNReal) := ⟨pn.one_le_toENNReal⟩

variable {M : Type} [Fintype M]

end PNorm

namespace LatticeFamily

variable {X : Type} (Λ : LatticeFamily X)

/-! ### Distances -/

/-! ### The real image of the lattice -/

/-- Coordinatewise `Int.cast` as a `ℤ`-linear map `ℤ^M → ℝ^M`. -/
def castₗ (M : Type) : (M → ℤ) →ₗ[ℤ] (M → ℝ) :=
  LinearMap.pi fun i => (Int.castAddHom ℝ).toIntLinearMap ∘ₗ LinearMap.proj i

@[simp] lemma castₗ_apply {M : Type} (v : M → ℤ) : castₗ M v = toReal v := rfl

/-- The lattice as a `ℤ`-submodule of `ℝ^M`: the image of `Λ.lattice` under coordinatewise
`Int.cast`. -/
def realLattice : Submodule ℤ (Λ.M → ℝ) := Λ.lattice.map (castₗ Λ.M)

/-! ### Discreteness and the `IsZLattice` structure -/

/-- The real image of the lattice lies in the `ℤ`-span of the standard basis of `ℝ^M`. -/
lemma realLattice_le_span_basisFun :
    Λ.realLattice ≤ Submodule.span ℤ (Set.range (Pi.basisFun ℝ Λ.M)) := by
  rintro _ ⟨v, -, rfl⟩
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro i
  exact ⟨v i, by simp [castₗ_apply, toReal]⟩

/-- Sublattices of `ℤ^M` are discrete subsets of `ℝ^M`. -/
instance discreteTopology_realLattice : DiscreteTopology Λ.realLattice := by
  have := ZSpan.discreteTopology_pi_basisFun (ι := Λ.M)
  exact DiscreteTopology.of_continuous_injective
    (f := Submodule.inclusion Λ.realLattice_le_span_basisFun)
    (continuous_subtype_val.subtype_mk _) (Submodule.inclusion_injective _)

end LatticeFamily

end LatticePrepro
