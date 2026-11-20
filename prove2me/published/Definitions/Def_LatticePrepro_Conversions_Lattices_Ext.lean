import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_Codes_Ext
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_ConstructionA_Ext
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Hadamard_Ext
import Definitions.Def_LatticePrepro_Conversions_Padding
import Definitions.Def_LatticePrepro_Conversions_Lattices

/-! Further definitions from `LatticePrepro/Conversions/Lattices.lean`, continuing `Def_LatticePrepro_Conversions_Lattices`. -/

namespace LatticePrepro

section Padded

open Finset

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

namespace LinearSystemFamily

/-- `k` with `b ≤ 2^k < 2b`, where `b` is the block size. -/
noncomputable def padK : ℕ := Nat.clog 2 L.blockSize

lemma blockSize_le_two_pow_padK : L.blockSize ≤ 2 ^ L.padK := Nat.le_pow_clog one_lt_two _

/-- Index set of a padded block. -/
abbrev PadIdx : Type := Hadamard.Idx L.padK

/-- Coordinates of the padded code: a block of the code and a position in `Fin k → ZMod 2`. -/
abbrev PadM : Type := (L.β ⊕ L.β) × L.PadIdx

/-- An enumeration of the code coordinates. -/
noncomputable def codeEnum : (L.ι ⊕ L.ι) ≃ Fin (Fintype.card (L.ι ⊕ L.ι)) := Fintype.equivFin _

/-- The position of a coordinate inside its block. -/
noncomputable def codeRank (i : L.ι ⊕ L.ι) : ℕ :=
  (univ.filter fun j => L.codeBlk j = L.codeBlk i ∧ L.codeEnum j < L.codeEnum i).card

lemma codeRank_lt_blockSize (i : L.ι ⊕ L.ι) : L.codeRank i < L.blockSize := by
  calc L.codeRank i ≤ ((univ.filter fun j => L.codeBlk j = L.codeBlk i).erase i).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hj ⊢
        refine ⟨fun hji => ?_, hj.1⟩
        subst hji
        exact lt_irrefl _ hj.2
    _ < (univ.filter fun j => L.codeBlk j = L.codeBlk i).card :=
        Finset.card_erase_lt_of_mem (by simp)
    _ = L.blockSize := L.card_codeBlk_fiber _

lemma codeRank_lt_of_lt {i j : L.ι ⊕ L.ι} (hs : L.codeBlk i = L.codeBlk j)
    (hij : L.codeEnum i < L.codeEnum j) : L.codeRank i < L.codeRank j := by
  unfold codeRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, by simp [hs, hij], by simp⟩
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact ⟨hl.1.trans hs, hl.2.trans hij⟩

lemma codeRank_inj {i j : L.ι ⊕ L.ι} (hs : L.codeBlk i = L.codeBlk j)
    (hr : L.codeRank i = L.codeRank j) : i = j := by
  by_contra hne
  have hne' : L.codeEnum i ≠ L.codeEnum j := fun h => hne (L.codeEnum.injective h)
  rcases lt_or_gt_of_ne hne' with h | h
  · exact absurd hr (L.codeRank_lt_of_lt hs h).ne
  · exact absurd hr (L.codeRank_lt_of_lt hs.symm h).ne'

/-- Positions `Fin (2^k)` as elements of `Fin k → ZMod 2`. -/
noncomputable def padIdxEquiv : Fin (2 ^ L.padK) ≃ L.PadIdx :=
  (Fintype.equivFinOfCardEq (Hadamard.card_Idx L.padK)).symm

/-- The block-respecting embedding of the code coordinates into the padded coordinates. -/
noncomputable def padEmbFn (i : L.ι ⊕ L.ι) : L.PadM :=
  (L.codeBlk i, L.padIdxEquiv ⟨L.codeRank i,
    lt_of_lt_of_le (L.codeRank_lt_blockSize i) L.blockSize_le_two_pow_padK⟩)

lemma padEmbFn_injective : Function.Injective L.padEmbFn := by
  intro i j h
  simp only [padEmbFn, Prod.mk.injEq] at h
  obtain ⟨hs, he⟩ := h
  have := L.padIdxEquiv.injective he
  exact L.codeRank_inj hs (Fin.mk.inj_iff.mp this)

/-- The padding embedding. -/
noncomputable def padEmb : L.ι ⊕ L.ι ↪ L.PadM := ⟨L.padEmbFn, L.padEmbFn_injective⟩

/-- The padded code. -/
noncomputable def padCode : Submodule (ZMod p) (L.PadM → ZMod p) :=
  Submodule.map (padMap L.padEmb) L.code

/-- The padded target. -/
noncomputable def padTarget (x : X) : L.PadM → ZMod p := padMap L.padEmb (L.codeTarget x)

end LinearSystemFamily

end Padded

section Cases

open Finset

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

namespace LinearSystemFamily

/-- The Construction A lattice family on the padded code (for `p ≤ 2`). -/
noncomputable abbrev latticeA : LatticeFamily X where
  M := L.PadM
  lattice := constructionA L.padCode
  target := fun x => liftZMod (L.padTarget x)

/-- The Hadamard-transformed lattice family (for `p > 2`). -/
noncomputable abbrev latticeH : LatticeFamily X where
  M := L.PadM
  lattice := Submodule.map (Hadamard.blockHadₗ L.padK) (constructionA L.padCode)
  target := fun x => Hadamard.blockHad L.padK (liftZMod (L.padTarget x))

end LinearSystemFamily

end Cases

end LatticePrepro
