import LatticePrepro.Basic.Blocks

/-!
# Padding codes by zero coordinates

Extension by zero along an injection `f : ι ↪ M` of coordinates, as a linear map
`padMap f : (ι → F) →ₗ[F] (M → F)`. It preserves Hamming weights and distances, binary vectors,
and block sparsity (when `f` respects blocks). This is the padding of the proof of Lemma 3.8,
which makes every block of a code have size a power of two.
-/

namespace LatticePrepro

open Finset

variable {F : Type*} [Semiring F] {ι M : Type*}

open Classical in
/-- Extension by zero along an embedding, as a linear map. -/
noncomputable def padMap (f : ι ↪ M) : (ι → F) →ₗ[F] (M → F) :=
  LinearMap.pi fun m => if h : ∃ i, f i = m then LinearMap.proj h.choose else 0

open Classical in
lemma padMap_apply (f : ι ↪ M) (v : ι → F) (m : M) :
    padMap f v m = if h : ∃ i, f i = m then v h.choose else 0 := by
  unfold padMap
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

lemma padMap_apply_emb (f : ι ↪ M) (v : ι → F) (i : ι) : padMap f v (f i) = v i := by
  rw [padMap_apply]
  split_ifs with h
  · congr 1
    exact f.injective (Classical.choose_spec h)
  · exact absurd ⟨i, rfl⟩ h

lemma padMap_apply_of_not (f : ι ↪ M) (v : ι → F) {m : M} (hm : ¬ ∃ i, f i = m) :
    padMap f v m = 0 := by
  rw [padMap_apply]
  simp [hm]

lemma isBinary_padMap (f : ι ↪ M) {v : ι → F} (hv : IsBinary v) : IsBinary (padMap f v) := by
  intro m
  by_cases hm : ∃ i, f i = m
  · obtain ⟨i, rfl⟩ := hm
    rw [padMap_apply_emb]
    exact hv i
  · left
    exact padMap_apply_of_not f v hm

variable [Fintype ι] [Fintype M] [DecidableEq F]

lemma filter_padMap_ne (f : ι ↪ M) (v w : ι → F) :
    (univ.filter fun m => padMap f v m ≠ padMap f w m) =
      (univ.filter fun i => v i ≠ w i).map f := by
  ext m
  simp only [mem_filter, mem_univ, true_and, mem_map]
  constructor
  · intro h
    by_cases hm : ∃ i, f i = m
    · obtain ⟨i, rfl⟩ := hm
      rw [padMap_apply_emb, padMap_apply_emb] at h
      exact ⟨i, h, rfl⟩
    · exact absurd (by rw [padMap_apply_of_not f v hm, padMap_apply_of_not f w hm]) h
  · rintro ⟨i, hi, rfl⟩
    rwa [padMap_apply_emb, padMap_apply_emb]

lemma hammingDist_padMap (f : ι ↪ M) (v w : ι → F) :
    hammingDist (padMap f v) (padMap f w) = hammingDist v w := by
  unfold hammingDist
  rw [filter_padMap_ne, card_map]

lemma hammingNorm_padMap (f : ι ↪ M) (v : ι → F) : hammingNorm (padMap f v) = hammingNorm v := by
  rw [← hammingDist_zero_right, ← hammingDist_zero_right, ← map_zero (padMap (F := F) f),
    hammingDist_padMap]

lemma blockSupport_padMap {β : Type*} [DecidableEq β] (f : ι ↪ M) (blk : ι → β) (blk' : M → β)
    (hf : ∀ i, blk' (f i) = blk i) (v : ι → F) (s : β) :
    blockSupport blk' (padMap f v) s = (blockSupport blk v s).map f := by
  ext m
  simp only [blockSupport, mem_filter, mem_univ, true_and, mem_map]
  constructor
  · rintro ⟨hs, h⟩
    by_cases hm : ∃ i, f i = m
    · obtain ⟨i, rfl⟩ := hm
      rw [hf] at hs
      rw [padMap_apply_emb] at h
      exact ⟨i, ⟨hs, h⟩, rfl⟩
    · exact absurd (padMap_apply_of_not f v hm) h
  · rintro ⟨i, ⟨hs, h⟩, rfl⟩
    rw [hf, padMap_apply_emb]
    exact ⟨hs, h⟩

lemma atMostOnePerBlock_padMap {β : Type*} [DecidableEq β] (f : ι ↪ M) (blk : ι → β)
    (blk' : M → β) (hf : ∀ i, blk' (f i) = blk i) {v : ι → F} (hv : AtMostOnePerBlock blk v) :
    AtMostOnePerBlock blk' (padMap f v) := by
  intro s
  rw [blockSupport_padMap f blk blk' hf, card_map]
  exact hv s

end LatticePrepro
