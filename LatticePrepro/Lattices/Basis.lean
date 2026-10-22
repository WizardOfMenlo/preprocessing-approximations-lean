import Mathlib

/-!
# Full-rank sublattices of `ℤ^M` have a basis

A `ℤ`-submodule `Λ ⊆ ℤ^M` containing `N · ℤ^M` for some `N > 0` is a full-rank lattice:
it has a `ℤ`-basis indexed by `Fin |M|`. This is the "integer basis" form in which the paper's
lattices are given (Lemma B.2, equation (B.2)); we only prove existence.
-/

namespace LatticePrepro

open Module

variable {M : Type} [Fintype M]

/-- The submodule `N • ℤ^M` has rank `|M|`. -/
lemma finrank_smul_top (N : ℤ) (hN : N ≠ 0) :
    finrank ℤ (Submodule.map (N • LinearMap.id : (M → ℤ) →ₗ[ℤ] (M → ℤ)) ⊤) = Fintype.card M := by
  have hinj : Function.Injective (N • LinearMap.id : (M → ℤ) →ₗ[ℤ] (M → ℤ)) := by
    intro v w h
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h
    exact smul_right_injective _ hN h
  rw [Submodule.map_top, LinearMap.finrank_range_of_inj hinj]
  simp

/-- A submodule of `ℤ^M` containing `N • ℤ^M` for some `N ≠ 0` has a basis indexed by `Fin |M|`. -/
theorem exists_basis_of_smul_le [DecidableEq M] (Λ : Submodule ℤ (M → ℤ)) {N : ℤ} (hN : N ≠ 0)
    (h : ∀ v : M → ℤ, N • v ∈ Λ) : Nonempty (Basis (Fin (Fintype.card M)) ℤ Λ) := by
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ M) Λ
  have hle : Submodule.map (N • LinearMap.id : (M → ℤ) →ₗ[ℤ] (M → ℤ)) ⊤ ≤ Λ := by
    rintro _ ⟨v, -, rfl⟩
    exact h v
  have h1 : Fintype.card M ≤ finrank ℤ Λ := by
    rw [← finrank_smul_top N hN]
    exact Submodule.finrank_mono hle
  have h2 : finrank ℤ Λ ≤ Fintype.card M := by
    calc finrank ℤ Λ ≤ finrank ℤ (M → ℤ) := Submodule.finrank_le Λ
      _ = Fintype.card M := by simp
  have hn : n = Fintype.card M := by
    have := finrank_eq_card_basis b
    rw [Fintype.card_fin] at this
    omega
  exact ⟨b.reindex (finCongr hn)⟩

end LatticePrepro
