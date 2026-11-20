import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem

/-!
# From linear systems to codes (Lemma 3.11, Appendix B.1)

Given a linear system family `A · v = b_x` over `𝔽_p` with columns `ι`, we build a fixed code
`𝒞 = ker A × {0} ⊆ 𝔽_p^{ι ⊕ ι}` and targets `y_x`: a solution `(v_0, 0)` of the system when one
exists, and `(0, 1)` otherwise. Then `y_x - 𝒞` is the set of solutions (padded by zeros), so

* YES instances have a binary vector `e` with `y_x - e ∈ 𝒞`, at most one nonzero entry per block
  and weight `≤ D`;
* NO instances have `dist(y_x, 𝒞) > g · D`.

The code is then extended by scalars to any finite field `F ⊇ 𝔽_p`, which preserves distances
to targets over `𝔽_p`.
-/

namespace LatticePrepro

/-- A fixed linear code with a target for every instance. -/
structure CodeFamily (F : Type) [Field F] (X : Type) where
  /-- Coordinates. -/
  M : Type
  [fintypeM : Fintype M]
  [decEqM : DecidableEq M]
  /-- The code. -/
  code : Submodule F (M → F)
  /-- The target for instance `x`. -/
  target : X → (M → F)

namespace CodeFamily

variable {F : Type} [Field F] {X : Type}

attribute [instance] fintypeM decEqM

/-- Hamming distance from a word to a code (Definition 3.1). -/
noncomputable def codeDist [DecidableEq F] {M : Type} [Fintype M] (y : M → F)
    (C : Submodule F (M → F)) : ℕ :=
  sInf {d | ∃ c ∈ C, hammingDist y c = d}

end CodeFamily

section OfSystem

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

/-- The code `ker A × {0}` of Lemma 3.11. -/
def LinearSystemFamily.code : Submodule (ZMod p) (L.ι ⊕ L.ι → ZMod p) :=
  LinearMap.ker ((L.A.comp (LinearMap.funLeft (ZMod p) (ZMod p) Sum.inl)).prod
    (LinearMap.funLeft (ZMod p) (ZMod p) Sum.inr))

open Classical in
/-- The target `y_x` of Lemma 3.11. -/
noncomputable def LinearSystemFamily.codeTarget (x : X) : L.ι ⊕ L.ι → ZMod p :=
  if h : ∃ v, L.IsSolution x v then Sum.elim h.choose 0 else Sum.elim 0 1

/-- The block of a code coordinate. -/
def LinearSystemFamily.codeBlk : L.ι ⊕ L.ι → L.β ⊕ L.β := Sum.map L.blk L.blk

end OfSystem

section Extend

variable {p : ℕ} [Fact p.Prime] {X : Type} (F : Type) [Field F] [Algebra (ZMod p) F]

/-- The `F`-linear code spanned by a code over `𝔽_p`, with the targets mapped along
`algebraMap`. -/
noncomputable def CodeFamily.extend (C : CodeFamily (ZMod p) X) : CodeFamily F X where
  M := C.M
  code := Submodule.span F ((fun c : C.M → ZMod p => fun i => algebraMap (ZMod p) F (c i)) '' C.code)
  target := fun x i => algebraMap (ZMod p) F (C.target x i)

end Extend

end LatticePrepro
