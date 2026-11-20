import Mathlib

/-!
# Walsh–Hadamard matrices and the block Hadamard map (Lemma B.2)

The Walsh–Hadamard matrix of order `2^k` is indexed by `Idx k = Fin k → ZMod 2`, with entries
`wh u w = (-1)^{⟨u, w⟩}`. It is symmetric with `H * H = 2^k • 1`. The block Hadamard map
`blockHad` applies `H` to every block of a vector indexed by `β × Idx k`; it is `ℤ`-linear,
satisfies `blockHad (blockHad v) = 2^k • v` and Parseval's identity
`∑ (blockHad v)² = 2^k ∑ v²`, and has entries bounded by the `ℓ_1` norm of the block.
-/

namespace LatticePrepro

namespace Hadamard

/-- The sign character `ZMod 2 → ℤ`, `0 ↦ 1`, `1 ↦ -1`. -/
def sgn (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

@[simp] lemma sgn_zero : sgn 0 = 1 := rfl

variable (k : ℕ)

/-- The index set of a Hadamard block of size `2^k`. -/
abbrev Idx : Type := Fin k → ZMod 2

/-- The inner product `⟨u, w⟩ = ∑ u_i w_i` over `ZMod 2`. -/
def ip (u w : Idx k) : ZMod 2 := ∑ i, u i * w i

/-- Entries `(-1)^{⟨u, w⟩}` of the Walsh–Hadamard matrix. -/
def wh (u w : Idx k) : ℤ := sgn (ip k u w)

/-- The Walsh–Hadamard matrix. -/
def whMat : Matrix (Idx k) (Idx k) ℤ := Matrix.of fun u w => wh k u w

section Block

variable {β : Type*}

/-- The block Hadamard map: apply the Walsh–Hadamard matrix to every block. -/
def blockHad (v : β × Idx k → ℤ) : β × Idx k → ℤ :=
  fun su => (whMat k).mulVec (fun w => v (su.1, w)) su.2

end Block

end Hadamard

end LatticePrepro
