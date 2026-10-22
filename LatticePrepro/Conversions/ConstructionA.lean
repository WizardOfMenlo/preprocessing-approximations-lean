import LatticePrepro.Basic.Blocks
import LatticePrepro.Basic.Hamming

/-!
# Construction A (Lemma B.2)

For a prime `p` and a code `𝒞 ⊆ 𝔽_p^M`, the lattice `Λ_𝒞 = {v ∈ ℤ^M : v mod p ∈ 𝒞}`.
We also define the lift `liftZMod y ∈ {0, …, p-1}^M` of a word `y ∈ 𝔽_p^M`, and prove the
residual bounds used in the lattice reduction: for `v ∈ Λ_𝒞`, the reduction of `t - v` modulo
`p` lies in `y - 𝒞`, and its Hamming weight is at most the number of nonzero coordinates of
`t - v`.
-/

namespace LatticePrepro

open Finset

variable {p : ℕ} [Fact p.Prime] {M : Type*}

/-- Coordinatewise reduction modulo `p` as a `ℤ`-linear map. -/
def redMod (p : ℕ) (M : Type*) : (M → ℤ) →ₗ[ℤ] (M → ZMod p) :=
  LinearMap.pi fun i => (Int.castAddHom (ZMod p)).toIntLinearMap ∘ₗ LinearMap.proj i

@[simp] lemma redMod_apply (v : M → ℤ) (i : M) : redMod p M v i = (v i : ZMod p) := rfl

/-- The Construction A lattice `Λ_𝒞 = {v : v mod p ∈ 𝒞}`. -/
def constructionA (C : Submodule (ZMod p) (M → ZMod p)) : Submodule ℤ (M → ℤ) :=
  (C.restrictScalars ℤ).comap (redMod p M)

lemma mem_constructionA {C : Submodule (ZMod p) (M → ZMod p)} {v : M → ℤ} :
    v ∈ constructionA C ↔ redMod p M v ∈ C := Iff.rfl

/-- `p · ℤ^M ⊆ Λ_𝒞`. -/
lemma natCast_smul_mem_constructionA (C : Submodule (ZMod p) (M → ZMod p)) (v : M → ℤ) :
    (p : ℤ) • v ∈ constructionA C := by
  rw [mem_constructionA]
  convert C.zero_mem
  funext i
  simp

/-- The lift `y ↦ (y_i.val)_i ∈ {0, …, p-1}^M`. -/
def liftZMod (y : M → ZMod p) : M → ℤ := fun i => ((y i).val : ℤ)

@[simp] lemma redMod_liftZMod (y : M → ZMod p) : redMod p M (liftZMod y) = y := by
  funext i
  simp [liftZMod]

lemma liftZMod_eq_zero_iff (y : M → ZMod p) (i : M) : liftZMod y i = 0 ↔ y i = 0 := by
  unfold liftZMod
  rw [Int.natCast_eq_zero, ZMod.val_eq_zero]

/-- The lift of a binary word is a `{0, 1}`-vector. -/
lemma liftZMod_binary {e : M → ZMod p} (he : IsBinary e) (i : M) :
    liftZMod e i = 0 ∨ liftZMod e i = 1 := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  rcases he i with h | h
  · left; unfold liftZMod; rw [h, ZMod.val_zero]; simp
  · right; unfold liftZMod; rw [h, ZMod.val_one]; simp

lemma abs_liftZMod_le_one {e : M → ZMod p} (he : IsBinary e) (i : M) : |liftZMod e i| ≤ 1 := by
  rcases liftZMod_binary he i with h | h <;> simp [h]

/-- The weight of a reduction is at most the number of nonzero coordinates. -/
lemma hammingNorm_redMod_le [Fintype M] (w : M → ℤ) :
    hammingNorm (redMod p M w) ≤ (univ.filter fun i => w i ≠ 0).card := by
  unfold hammingNorm
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, fun h0 => hi.2 ?_⟩
  simp [h0]

/-- The residual `t - v` of a lattice vector `v ∈ Λ_𝒞` against the lift `t` of `y` reduces to
`y - (v mod p)`, a word at Hamming distance `hammingDist y (v mod p)` from `y`, with
`v mod p ∈ 𝒞`. -/
lemma redMod_lift_sub [Fintype M] (C : Submodule (ZMod p) (M → ZMod p)) (y : M → ZMod p)
    {v : M → ℤ} (hv : v ∈ constructionA C) :
    redMod p M v ∈ C ∧ hammingNorm (redMod p M (liftZMod y - v)) = hammingDist y (redMod p M v) := by
  refine ⟨hv, ?_⟩
  rw [map_sub, redMod_liftZMod, hammingNorm_sub_eq_hammingDist]

/-- YES direction of Construction A: `t - ẽ ∈ Λ_𝒞` when `y - e ∈ 𝒞`. -/
lemma lift_sub_lift_mem_constructionA (C : Submodule (ZMod p) (M → ZMod p)) {y e : M → ZMod p}
    (h : y - e ∈ C) : liftZMod y - liftZMod e ∈ constructionA C := by
  rw [mem_constructionA, map_sub, redMod_liftZMod, redMod_liftZMod]
  exact h

end LatticePrepro
