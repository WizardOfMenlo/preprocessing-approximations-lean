import LatticePrepro.Conversions.Lattices

/-!
# Distance from a target to a lattice

The paper (Definition 2.1) measures the distance from a target `t` to a lattice `Λ` as
`dist_p(t, Λ) = min_{v ∈ Λ} ‖t − v‖_p`. For a `LatticeFamily`, we define
`latticeDist pn x = ⨅ v ∈ Λ, ‖t_x − v‖_p` and show that the infimum is attained
(`exists_dist_eq_latticeDist`): the lattice vectors within any given distance of `t_x` form a
finite set of integer vectors, since every coordinate is bounded by the `ℓ_p` norm.

The consequences `latticeDist_le_of_exists` and `lt_latticeDist_of_forall` translate the
"some lattice vector within `R`" / "every lattice vector beyond `γ R`" form of the main theorems
into bounds on `dist_p(t_x, Λ)`.
-/

namespace LatticePrepro

namespace PNorm

variable {M : Type} [Fintype M]

/-- Every coordinate is bounded in absolute value by the `ℓ_p` norm. -/
lemma abs_apply_le_norm (pn : PNorm) (w : M → ℝ) (i : M) : |w i| ≤ pn.norm w := by
  cases pn with
  | fin p hp =>
    show |w i| ≤ (∑ j, |w j| ^ p) ^ (1 / p)
    have hp0 : 0 < p := by linarith
    have h1 : |w i| ^ p ≤ ∑ j, |w j| ^ p :=
      Finset.single_le_sum (f := fun j => |w j| ^ p)
        (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
    calc |w i| = (|w i| ^ p) ^ (1 / p) := by
          rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp0.ne', Real.rpow_one]
      _ ≤ (∑ j, |w j| ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) h1 (by positivity)
  | inf =>
    show |w i| ≤ ⨆ j, |w j|
    exact le_ciSup (Set.finite_range fun j => |w j|).bddAbove i

end PNorm

namespace LatticeFamily

variable {X : Type} (Λ : LatticeFamily X) (pn : PNorm) (x : X)

/-- The distance `dist_p(t_x, Λ) = inf_{v ∈ Λ} ‖t_x − v‖_p` from the target to the lattice
(Definition 2.1). The infimum is attained (`exists_dist_eq_latticeDist`). -/
noncomputable def latticeDist : ℝ := ⨅ v : Λ.lattice, Λ.dist pn x v

lemma dist_nonneg (v : Λ.M → ℤ) : 0 ≤ Λ.dist pn x v := pn.norm_nonneg _

lemma bddBelow_range_dist : BddBelow (Set.range fun v : Λ.lattice => Λ.dist pn x v) :=
  ⟨0, by rintro _ ⟨v, rfl⟩; exact Λ.dist_nonneg pn x v⟩

instance : Nonempty Λ.lattice := ⟨0⟩

theorem latticeDist_le {v : Λ.M → ℤ} (hv : v ∈ Λ.lattice) :
    Λ.latticeDist pn x ≤ Λ.dist pn x v :=
  ciInf_le (Λ.bddBelow_range_dist pn x) ⟨v, hv⟩

theorem le_latticeDist {d : ℝ} (h : ∀ v ∈ Λ.lattice, d ≤ Λ.dist pn x v) :
    d ≤ Λ.latticeDist pn x :=
  le_ciInf fun v => h v v.2

theorem latticeDist_nonneg : 0 ≤ Λ.latticeDist pn x :=
  Λ.le_latticeDist pn x fun v _ => Λ.dist_nonneg pn x v

theorem latticeDist_le_of_exists {R : ℝ} (h : ∃ v ∈ Λ.lattice, Λ.dist pn x v ≤ R) :
    Λ.latticeDist pn x ≤ R := by
  obtain ⟨v, hv, hvR⟩ := h
  exact (Λ.latticeDist_le pn x hv).trans hvR

/-- The lattice vectors within distance `K` of the target form a finite set: every coordinate of
`t_x - v` is bounded by `K`. -/
lemma finite_dist_le (K : ℝ) : {v : Λ.M → ℤ | v ∈ Λ.lattice ∧ Λ.dist pn x v ≤ K}.Finite := by
  refine Set.Finite.subset (Set.Finite.pi' (κ := fun _ : Λ.M => ℤ)
    (t := fun i => Set.Icc (Λ.target x i - ⌈K⌉) (Λ.target x i + ⌈K⌉))
    fun _ => Set.finite_Icc _ _) ?_
  intro v hv i
  have h1 := pn.abs_apply_le_norm (toReal (Λ.target x - v)) i
  have h2 : ((|Λ.target x i - v i| : ℤ) : ℝ) ≤ K := by
    rw [Int.cast_abs]
    exact h1.trans hv.2
  have h3 : |Λ.target x i - v i| ≤ ⌈K⌉ := Int.cast_le.mp (h2.trans (Int.le_ceil K))
  rw [abs_le] at h3
  simp only [Set.mem_Icc]
  omega

/-- **The infimum is attained**: some lattice vector realizes `dist_p(t_x, Λ)`. -/
theorem exists_dist_eq_latticeDist : ∃ v ∈ Λ.lattice, Λ.dist pn x v = Λ.latticeDist pn x := by
  set T : Set (Λ.M → ℤ) := {v | v ∈ Λ.lattice ∧ Λ.dist pn x v ≤ Λ.dist pn x 0} with hT
  have hT0 : (0 : Λ.M → ℤ) ∈ T := ⟨Λ.lattice.zero_mem, le_rfl⟩
  obtain ⟨v, ⟨hvL, -⟩, hmin⟩ :=
    Set.exists_min_image T (Λ.dist pn x) (Λ.finite_dist_le pn x _) ⟨0, hT0⟩
  refine ⟨v, hvL, le_antisymm ?_ (Λ.latticeDist_le pn x hvL)⟩
  refine Λ.le_latticeDist pn x fun w hw => ?_
  by_cases hwK : Λ.dist pn x w ≤ Λ.dist pn x 0
  · exact hmin w ⟨hw, hwK⟩
  · exact (hmin 0 hT0).trans (not_le.mp hwK).le

theorem lt_latticeDist_of_forall {d : ℝ} (h : ∀ v ∈ Λ.lattice, d < Λ.dist pn x v) :
    d < Λ.latticeDist pn x := by
  obtain ⟨v, hv, hd⟩ := Λ.exists_dist_eq_latticeDist pn x
  rw [← hd]
  exact h v hv

end LatticeFamily

end LatticePrepro
