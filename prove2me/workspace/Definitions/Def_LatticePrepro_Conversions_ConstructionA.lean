import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks

/-!
# Construction A (Lemma B.1)

For a prime `p` and a code `𝒞 ⊆ 𝔽_p^M`, the lattice `Λ_𝒞 = {v ∈ ℤ^M : v mod p ∈ 𝒞}`.
We also define the lift `liftZMod y ∈ {0, …, p-1}^M` of a word `y ∈ 𝔽_p^M`, and prove the
residual bounds used in the lattice reduction: for `v ∈ Λ_𝒞`, the reduction of `t - v` modulo
`p` lies in `y - 𝒞`, and its Hamming weight is at most the number of nonzero coordinates of
`t - v`.
-/

namespace LatticePrepro

open Finset

variable {p : ℕ} [Fact p.Prime] {M : Type*}

/-- The lift `y ↦ (y_i.val)_i ∈ {0, …, p-1}^M`. -/
def liftZMod (y : M → ZMod p) : M → ℤ := fun i => ((y i).val : ℤ)

end LatticePrepro
