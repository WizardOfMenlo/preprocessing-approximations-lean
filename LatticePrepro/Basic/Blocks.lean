import Mathlib

/-!
# Block-sparse vectors

Vectors `y : ι → F` whose coordinates are partitioned into blocks by a map `blk : ι → β`.
We define binary vectors and vectors with at most (exactly) one nonzero entry per block,
and relate them to the Hamming weight `hammingNorm`.
-/

namespace LatticePrepro

variable {ι β F : Type*}

/-- A vector is binary if every coordinate is `0` or `1`. -/
def IsBinary [Zero F] [One F] (y : ι → F) : Prop := ∀ i, y i = 0 ∨ y i = 1

lemma IsBinary.mul_of_binary [MulZeroOneClass F] {c : F} (hc : c = 0 ∨ c = 1) {y : ι → F}
    (hy : IsBinary y) : IsBinary (fun i => c * y i) := by
  intro i
  rcases hc with rfl | rfl
  · simp
  · simpa using hy i

lemma isBinary_zero [Zero F] [One F] : IsBinary (0 : ι → F) := fun _ => Or.inl rfl

variable [Fintype ι] [DecidableEq β]

/-- The nonzero coordinates of `y` inside the block `s`. -/
def blockSupport [Zero F] [DecidableEq F] (blk : ι → β) (y : ι → F) (s : β) : Finset ι :=
  Finset.univ.filter fun i => blk i = s ∧ y i ≠ 0

/-- At most one nonzero coordinate in every block. -/
def AtMostOnePerBlock [Zero F] [DecidableEq F] (blk : ι → β) (y : ι → F) : Prop :=
  ∀ s, (blockSupport blk y s).card ≤ 1

/-- Exactly one nonzero coordinate in every block. -/
def ExactlyOnePerBlock [Zero F] [DecidableEq F] (blk : ι → β) (y : ι → F) : Prop :=
  ∀ s, (blockSupport blk y s).card = 1

section

variable [Zero F] [DecidableEq F] (blk : ι → β)

lemma ExactlyOnePerBlock.atMostOne {y : ι → F} (h : ExactlyOnePerBlock blk y) :
    AtMostOnePerBlock blk y := fun s => (h s).le

lemma atMostOnePerBlock_zero : AtMostOnePerBlock blk (0 : ι → F) := by
  intro s; simp [blockSupport]

/-- The Hamming weight is the sum of the block supports. -/
lemma hammingNorm_eq_sum_blockSupport [Fintype β] (y : ι → F) :
    hammingNorm y = ∑ s, (blockSupport blk y s).card := by
  classical
  unfold hammingNorm blockSupport
  rw [Finset.card_eq_sum_card_fiberwise (f := blk) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  ext i
  simp [and_comm]

lemma hammingNorm_le_card_of_atMostOnePerBlock [Fintype β] {y : ι → F}
    (h : AtMostOnePerBlock blk y) : hammingNorm y ≤ Fintype.card β := by
  rw [hammingNorm_eq_sum_blockSupport blk y]
  calc ∑ s, (blockSupport blk y s).card ≤ ∑ _s : β, 1 := Finset.sum_le_sum fun s _ => h s
    _ = Fintype.card β := by simp

end

section Scalar

variable [MulZeroOneClass F] [DecidableEq F] [NoZeroDivisors F] (blk : ι → β)

lemma blockSupport_smul_subset (c : F) (y : ι → F) (s : β) :
    blockSupport blk (fun i => c * y i) s ⊆ blockSupport blk y s := by
  intro i
  simp only [blockSupport, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, mul_eq_zero,
    not_or]
  tauto

lemma AtMostOnePerBlock.smul {y : ι → F} (h : AtMostOnePerBlock blk y) (c : F) :
    AtMostOnePerBlock blk (fun i => c * y i) := fun s =>
  (Finset.card_le_card (blockSupport_smul_subset blk c y s)).trans (h s)

end Scalar

end LatticePrepro
