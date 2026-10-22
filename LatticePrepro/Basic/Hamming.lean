import Mathlib

/-!
# Hamming weight and distance on sum types and differences
-/

namespace LatticePrepro

/-- The Hamming weight of a vector on a sum type is the sum of the weights of its halves. -/
lemma hammingNorm_sum_elim {α β γ : Type*} [Fintype α] [Fintype β] [Zero γ] [DecidableEq γ]
    (a : α → γ) (b : β → γ) : hammingNorm (Sum.elim a b) = hammingNorm a + hammingNorm b := by
  simp only [hammingNorm, Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

/-- The Hamming distance of vectors on a sum type is the sum of the distances of their halves. -/
lemma hammingDist_sum_elim {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (a c : α → γ) (b d : β → γ) :
    hammingDist (Sum.elim a b) (Sum.elim c d) = hammingDist a c + hammingDist b d := by
  simp only [hammingDist, Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

/-- The Hamming weight of a difference is the Hamming distance. -/
lemma hammingNorm_sub_eq_hammingDist {M : Type*} [Fintype M] {R : Type*} [AddGroup R] [DecidableEq R]
    (a b : M → R) :
    hammingNorm (a - b) = hammingDist a b := by
  simp [hammingNorm, hammingDist, sub_eq_zero]

end LatticePrepro
