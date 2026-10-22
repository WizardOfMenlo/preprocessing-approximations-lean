import Mathlib

/-!
# Coefficient functions and moments

A *coefficient function* (Definition 4.1 of the paper) is a finitely supported function from a
field `Ω` to a coefficient ring `F` (in the paper, the prime field `𝔽_p`). We model it as a
`Finsupp` `Ω →₀ F`. Its `k`-th moment (Definition 4.2) is `∑ α, f α • α ^ k ∈ Ω`.

The main facts proved here are:
* `moment` is `F`-linear (`momentₗ`);
* the Vandermonde identification lemma (Lemma 4.3): a function supported on at most `t` points
  whose first `t` moments vanish is zero;
* the binomial identity for the moments of a translation difference (equation (4.4)).
-/

namespace LatticePrepro

open Finsupp

section Moment

variable {F Ω : Type*} [CommRing F] [CommRing Ω] [Algebra F Ω]

/-- The `k`-th moment `∑ α, f α • α ^ k` of a finitely supported `f : Ω →₀ F`
(Definition 4.2; with the convention `0 ^ 0 = 1`). -/
noncomputable def moment (f : Ω →₀ F) (k : ℕ) : Ω :=
  f.sum fun α c => c • α ^ k

/-- The moment map as an `F`-linear map. -/
noncomputable def momentₗ (k : ℕ) : (Ω →₀ F) →ₗ[F] Ω :=
  Finsupp.lsum F fun α => LinearMap.toSpanSingleton F Ω (α ^ k)

@[simp] lemma momentₗ_apply (f : Ω →₀ F) (k : ℕ) : momentₗ k f = moment f k := by
  simp only [momentₗ, moment, Finsupp.lsum_apply]
  rfl

lemma moment_eq_sum (f : Ω →₀ F) (k : ℕ) :
    moment f k = ∑ α ∈ f.support, f α • α ^ k := rfl

lemma moment_eq_sum_of_subset (f : Ω →₀ F) (k : ℕ) {s : Finset Ω} (hs : f.support ⊆ s) :
    moment f k = ∑ α ∈ s, f α • α ^ k := by
  rw [moment_eq_sum]
  exact Finset.sum_subset hs fun α _ hα => by
    simp [Finsupp.notMem_support_iff.mp hα]

@[simp] lemma moment_zero (k : ℕ) : moment (0 : Ω →₀ F) k = 0 := by
  simp [moment]

@[simp] lemma moment_single (α : Ω) (c : F) (k : ℕ) :
    moment (single α c) k = c • α ^ k := by
  simp [moment, sum_single_index]

lemma moment_add (f g : Ω →₀ F) (k : ℕ) : moment (f + g) k = moment f k + moment g k := by
  simp only [← momentₗ_apply, map_add]

lemma moment_sub (f g : Ω →₀ F) (k : ℕ) : moment (f - g) k = moment f k - moment g k := by
  simp only [← momentₗ_apply, map_sub]

lemma moment_neg (f : Ω →₀ F) (k : ℕ) : moment (-f) k = - moment f k := by
  simp only [← momentₗ_apply, map_neg]

lemma moment_smul (c : F) (f : Ω →₀ F) (k : ℕ) : moment (c • f) k = c • moment f k := by
  simp only [← momentₗ_apply, map_smul]

lemma moment_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Ω →₀ F) (k : ℕ) :
    moment (∑ i ∈ s, f i) k = ∑ i ∈ s, moment (f i) k := by
  simp only [← momentₗ_apply, map_sum]

/-- Moment of the point indicator `single α 1` is `α ^ k`. -/
lemma moment_indicator (α : Ω) (k : ℕ) : moment (single α (1 : F)) k = α ^ k := by
  simp

/-- Extend the scalars of a coefficient function along `algebraMap F Ω`. -/
noncomputable def extendScalars (f : Ω →₀ F) : Ω →₀ Ω :=
  f.mapRange (algebraMap F Ω) (map_zero _)

@[simp] lemma extendScalars_apply (f : Ω →₀ F) (α : Ω) :
    extendScalars f α = algebraMap F Ω (f α) := rfl

lemma moment_extendScalars (f : Ω →₀ F) (k : ℕ) : moment (extendScalars f) k = moment f k := by
  unfold moment extendScalars
  rw [sum_mapRange_index (by simp)]
  simp [Algebra.smul_def]

lemma support_extendScalars_subset (f : Ω →₀ F) : (extendScalars f).support ⊆ f.support :=
  Finsupp.support_mapRange

lemma support_extendScalars (f : Ω →₀ F) (h : Function.Injective (algebraMap F Ω)) :
    (extendScalars f).support = f.support :=
  Finsupp.support_mapRange_of_injective (map_zero _) f h

@[simp] lemma extendScalars_zero : extendScalars (0 : Ω →₀ F) = 0 := by
  ext; simp

lemma extendScalars_add (f g : Ω →₀ F) :
    extendScalars (f + g) = extendScalars f + extendScalars g := by
  ext; simp

lemma extendScalars_sub (f g : Ω →₀ F) :
    extendScalars (f - g) = extendScalars f - extendScalars g := by
  ext; simp

lemma extendScalars_single (α : Ω) (c : F) :
    extendScalars (single α c) = single α (algebraMap F Ω c) := by
  simp [extendScalars, Finsupp.mapRange_single]

lemma extendScalars_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Ω →₀ F) :
    extendScalars (∑ i ∈ s, f i) = ∑ i ∈ s, extendScalars (f i) := by
  ext; simp [Finsupp.finsetSum_apply]

lemma extendScalars_eq_zero_iff (f : Ω →₀ F) (h : Function.Injective (algebraMap F Ω)) :
    extendScalars f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    ext α
    have := congrArg (fun g => g α) hf
    simp only [extendScalars_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    exact h (by simpa using this)
  · rintro rfl; simp

end Moment

section Translation

variable {F Ω : Type*} [CommRing F] [CommRing Ω]

/-- The translation `α ↦ f (α - c)` of a coefficient function, i.e. the push-forward of `f`
along `α ↦ α + c`. -/
noncomputable def translate (c : Ω) (f : Ω →₀ F) : Ω →₀ F :=
  f.mapDomain (· + c)

lemma translate_apply (c : Ω) (f : Ω →₀ F) (α : Ω) : translate c f α = f (α - c) := by
  unfold translate
  have := Finsupp.mapDomain_apply_of_injective (add_left_injective c) f (α - c)
  simpa only [sub_add_cancel] using this

lemma support_translate (c : Ω) (f : Ω →₀ F) :
    (translate c f).support = f.support.map (addRightEmbedding c) := by
  classical
  unfold translate
  rw [Finsupp.mapDomain_support_of_injective (add_left_injective c), Finset.map_eq_image]
  rfl

lemma card_support_translate (c : Ω) (f : Ω →₀ F) :
    (translate c f).support.card = f.support.card := by
  rw [support_translate, Finset.card_map]

lemma card_support_translate_sub_le (c : Ω) (f : Ω →₀ F) :
    (translate c f - f).support.card ≤ 2 * f.support.card := by
  classical
  calc (translate c f - f).support.card
      ≤ ((translate c f).support ∪ f.support).card := Finset.card_le_card Finsupp.support_sub
    _ ≤ (translate c f).support.card + f.support.card := Finset.card_union_le _ _
    _ = 2 * f.support.card := by rw [card_support_translate]; ring

@[simp] lemma translate_single (c α : Ω) (a : F) :
    translate c (single α a) = single (α + c) a := by
  unfold translate; simp [Finsupp.mapDomain_single]

lemma translate_smul (c : Ω) (a : F) (f : Ω →₀ F) : translate c (a • f) = a • translate c f := by
  unfold translate; simp [Finsupp.mapDomain_smul]

variable [Algebra F Ω]

/-- The binomial identity (4.4): the moments of a translation are linear combinations of the
lower-order moments. -/
lemma moment_translate (c : Ω) (f : Ω →₀ F) (k : ℕ) :
    moment (translate c f) k = ∑ j ∈ Finset.range (k + 1), (k.choose j : Ω) * c ^ (k - j) * moment f j := by
  unfold moment translate
  rw [Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [add_pow, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

/-- The moments of a translation difference, with the top term cancelled. -/
lemma moment_translate_sub (c : Ω) (f : Ω →₀ F) (k : ℕ) :
    moment (translate c f - f) k =
      ∑ j ∈ Finset.range k, (k.choose j : Ω) * c ^ (k - j) * moment f j := by
  rw [moment_sub, moment_translate, Finset.sum_range_succ]
  simp

end Translation

section Identification

variable {Ω : Type*} [Field Ω]

/-- **Vandermonde identification** (Lemma 4.3). A finitely supported `g : Ω →₀ Ω` supported on
at most `t` points whose moments of order `< t` all vanish is identically zero. -/
theorem eq_zero_of_moment_eq_zero (g : Ω →₀ Ω) {t : ℕ} (hs : g.support.card ≤ t)
    (h : ∀ k < t, moment g k = 0) : g = 0 := by
  classical
  set s := g.support with hs_def
  set e : Fin s.card ≃ s := s.equivFin.symm
  let v : Fin s.card → Ω := fun j => (e j : Ω)
  have hv : Function.Injective v := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  let w : Fin s.card → Ω := fun j => g (e j)
  have hw : Matrix.vecMul w (Matrix.vandermonde v) = 0 := by
    funext k
    have hk : (k : ℕ) < t := lt_of_lt_of_le k.isLt hs
    have hmom := h k hk
    rw [moment_eq_sum] at hmom
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    rw [← hmom, ← Finset.sum_coe_sort s, ← e.sum_comp]
    simp [w, v, smul_eq_mul]
  have hdet : (Matrix.vandermonde v).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have hw0 : w = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hw
  ext α
  by_cases hα : α ∈ g.support
  · have := congrFun hw0 (e.symm ⟨α, hα⟩)
    simpa [w] using this
  · simpa using Finsupp.notMem_support_iff.mp hα

/-- Two functions whose difference is supported on at most `t` points and whose moments of
order `< t` agree are equal. -/
theorem eq_of_moment_eq (f g : Ω →₀ Ω) {t : ℕ} (hs : (f - g).support.card ≤ t)
    (h : ∀ k < t, moment f k = moment g k) : f = g := by
  have := eq_zero_of_moment_eq_zero (f - g) hs fun k hk => by
    rw [moment_sub, h k hk, sub_self]
  exact sub_eq_zero.mp this

end Identification

end LatticePrepro
