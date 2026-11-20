import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks

/-!
# Padding codes by zero coordinates

Extension by zero along an injection `f : ι ↪ M` of coordinates, as a linear map
`padMap f : (ι → F) →ₗ[F] (M → F)`. It preserves Hamming weights and distances, binary vectors,
and block sparsity (when `f` respects blocks). This is the padding of the proof of Lemma 3.12,
which makes every block of a code have size a power of two.
-/

namespace LatticePrepro

open Finset

variable {F : Type*} [Semiring F] {ι M : Type*}

open Classical in
/-- Extension by zero along an embedding, as a linear map. -/
noncomputable def padMap (f : ι ↪ M) : (ι → F) →ₗ[F] (M → F) :=
  LinearMap.pi fun m => if h : ∃ i, f i = m then LinearMap.proj h.choose else 0

variable [Fintype ι] [Fintype M] [DecidableEq F]

end LatticePrepro
