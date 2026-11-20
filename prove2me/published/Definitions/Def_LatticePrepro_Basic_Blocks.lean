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

end LatticePrepro
