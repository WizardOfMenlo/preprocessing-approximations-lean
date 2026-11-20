import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

/-! Further definitions from `LatticePrepro/Conversions/Codes.lean`, continuing `Def_LatticePrepro_Conversions_Codes`. -/

namespace LatticePrepro

section OfSystem

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

/-- The code family of Lemma 3.11 over the prime field. -/
noncomputable def LinearSystemFamily.toCodeFamily : CodeFamily (ZMod p) X where
  M := L.ι ⊕ L.ι
  code := L.code
  target := L.codeTarget

lemma LinearSystemFamily.card_codeBlk_fiber (s : L.β ⊕ L.β) :
    (Finset.univ.filter fun i => L.codeBlk i = s).card = L.blockSize := by
  rcases s with t | t
  · rw [← L.card_fiber t, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.inl.injEq, reduceCtorEq,
      ite_false, Finset.sum_const_zero, add_zero]
  · rw [← L.card_fiber t, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.inr.injEq, reduceCtorEq,
      ite_false, Finset.sum_const_zero, zero_add]

end OfSystem

end LatticePrepro
