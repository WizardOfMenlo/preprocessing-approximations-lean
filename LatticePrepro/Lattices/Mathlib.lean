import LatticePrepro.Lattices.Distance

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
  (`LatticeFamily.isZLattice_realLattice`), which is the full-rank condition of Lemma 3.8.
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

/-- `PNorm.norm` is the norm of `PiLp p (fun _ : M => ℝ)`. -/
theorem norm_eq_piLp (pn : PNorm) (v : M → ℝ) :
    pn.norm v = ‖(toLp pn.toENNReal v : PiLp pn.toENNReal fun _ : M => ℝ)‖ := by
  cases pn with
  | fin p hp =>
    have hp0 : 0 < p := by linarith
    have ht : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
    show (∑ i, |v i| ^ p) ^ (1 / p) =
      ‖(toLp (ENNReal.ofReal p) v : PiLp (ENNReal.ofReal p) fun _ : M => ℝ)‖
    rw [PiLp.norm_eq_sum (by rw [ht]; exact hp0)]
    simp only [ht, Real.norm_eq_abs]
  | inf =>
    show (⨆ i, |v i|) = ‖(toLp ⊤ v : PiLp ⊤ fun _ : M => ℝ)‖
    rw [PiLp.norm_eq_ciSup]
    simp only [Real.norm_eq_abs]

end PNorm

namespace LatticeFamily

variable {X : Type} (Λ : LatticeFamily X)

/-! ### Distances -/

lemma toReal_sub {M : Type} (v w : M → ℤ) : toReal (v - w) = toReal v - toReal w := by
  funext i
  simp [toReal]

/-- `LatticeFamily.dist` is the distance in `PiLp p (fun _ : M => ℝ)`. -/
theorem dist_eq_piLp (pn : PNorm) (x : X) (v : Λ.M → ℤ) :
    Λ.dist pn x v =
      Dist.dist (toLp pn.toENNReal (toReal (Λ.target x)) : PiLp pn.toENNReal fun _ => ℝ)
        (toLp pn.toENNReal (toReal v)) := by
  rw [dist_eq_norm, ← toLp_sub, LatticeFamily.dist, pn.norm_eq_piLp, toReal_sub]

/-! ### The real image of the lattice -/

/-- Coordinatewise `Int.cast` as a `ℤ`-linear map `ℤ^M → ℝ^M`. -/
def castₗ (M : Type) : (M → ℤ) →ₗ[ℤ] (M → ℝ) :=
  LinearMap.pi fun i => (Int.castAddHom ℝ).toIntLinearMap ∘ₗ LinearMap.proj i

@[simp] lemma castₗ_apply {M : Type} (v : M → ℤ) : castₗ M v = toReal v := rfl

/-- The lattice as a `ℤ`-submodule of `ℝ^M`: the image of `Λ.lattice` under coordinatewise
`Int.cast`. -/
def realLattice : Submodule ℤ (Λ.M → ℝ) := Λ.lattice.map (castₗ Λ.M)

lemma mem_realLattice_iff (w : Λ.M → ℝ) :
    w ∈ Λ.realLattice ↔ ∃ v ∈ Λ.lattice, toReal v = w :=
  Submodule.mem_map

lemma toReal_mem_realLattice {v : Λ.M → ℤ} (hv : v ∈ Λ.lattice) : toReal v ∈ Λ.realLattice :=
  Submodule.mem_map_of_mem hv

/-- `latticeDist` is Mathlib's `Metric.infDist` from the target to the real image of the lattice,
in `PiLp p (fun _ : M => ℝ)`. -/
theorem latticeDist_eq_infDist (pn : PNorm) (x : X) :
    Λ.latticeDist pn x =
      Metric.infDist (toLp pn.toENNReal (toReal (Λ.target x)) : PiLp pn.toENNReal fun _ => ℝ)
        (toLp pn.toENNReal '' (Λ.realLattice : Set (Λ.M → ℝ))) := by
  rw [Metric.infDist_eq_iInf, LatticeFamily.latticeDist]
  set t : PiLp pn.toENNReal fun _ : Λ.M => ℝ := toLp pn.toENNReal (toReal (Λ.target x)) with ht
  set s : Set (PiLp pn.toENNReal fun _ : Λ.M => ℝ) :=
    toLp pn.toENNReal '' (Λ.realLattice : Set (Λ.M → ℝ)) with hs
  have : Nonempty s := ⟨⟨toLp pn.toENNReal (toReal 0), toReal 0,
    Λ.toReal_mem_realLattice Λ.lattice.zero_mem, rfl⟩⟩
  have hbdd : BddBelow (Set.range fun y : s => Dist.dist t y) :=
    ⟨0, by rintro _ ⟨y, rfl⟩; exact _root_.dist_nonneg⟩
  apply le_antisymm
  · refine le_ciInf fun y => ?_
    obtain ⟨y, w, hw, rfl⟩ := y
    obtain ⟨v, hv, rfl⟩ := (Λ.mem_realLattice_iff w).mp hw
    rw [← Λ.dist_eq_piLp pn x v]
    exact Λ.latticeDist_le pn x hv
  · refine le_ciInf fun v => ?_
    rw [Λ.dist_eq_piLp pn x v]
    exact ciInf_le hbdd ⟨toLp pn.toENNReal (toReal v), toReal v, Λ.toReal_mem_realLattice v.2, rfl⟩

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

/-- A lattice containing `N · ℤ^M` for some `N > 0` is an `IsZLattice`: a discrete `ℤ`-submodule
of `ℝ^M` spanning `ℝ^M` (the full-rank condition of Lemma 3.8). -/
theorem isZLattice_realLattice {N : ℕ} (hN : 0 < N)
    (h : ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice) : IsZLattice ℝ Λ.realLattice := by
  refine ⟨eq_top_iff.mpr ?_⟩
  rw [← (Pi.basisFun ℝ Λ.M).span_eq]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  have hmem : toReal ((N : ℤ) • Pi.single i 1) ∈ Λ.realLattice :=
    Λ.toReal_mem_realLattice (h _)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hbasis : Pi.basisFun ℝ Λ.M i = (N : ℝ)⁻¹ • toReal ((N : ℤ) • Pi.single i 1) := by
    funext j
    simp only [Pi.basisFun_apply, Pi.smul_apply, toReal, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp [hNr]
  rw [hbasis]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end LatticeFamily

end LatticePrepro
