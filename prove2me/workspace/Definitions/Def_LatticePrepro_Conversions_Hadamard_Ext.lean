import Mathlib
import Definitions.Def_LatticePrepro_Conversions_Hadamard

/-! Further definitions from `LatticePrepro/Conversions/Hadamard.lean`, continuing `Def_LatticePrepro_Conversions_Hadamard`. -/

namespace LatticePrepro

namespace Hadamard

variable (k : ℕ)

lemma card_Idx : Fintype.card (Idx k) = 2 ^ k := by
  simp [ZMod.card]

section Block

variable {β : Type*}

lemma blockHad_apply (v : β × Idx k → ℤ) (su : β × Idx k) :
    blockHad k v su = ∑ w, wh k su.2 w * v (su.1, w) := by
  simp [blockHad, Matrix.mulVec, dotProduct, whMat]

lemma blockHad_add (v w : β × Idx k → ℤ) : blockHad k (v + w) = blockHad k v + blockHad k w := by
  funext su; simp [blockHad_apply, mul_add, Finset.sum_add_distrib]

lemma blockHad_smul (c : ℤ) (v : β × Idx k → ℤ) : blockHad k (c • v) = c • blockHad k v := by
  funext su; simp [blockHad_apply, Finset.mul_sum, mul_left_comm]

/-- The block Hadamard map as a `ℤ`-linear map. -/
def blockHadₗ : (β × Idx k → ℤ) →ₗ[ℤ] (β × Idx k → ℤ) where
  toFun := blockHad k
  map_add' := blockHad_add k
  map_smul' := blockHad_smul k

@[simp] lemma blockHadₗ_apply (v : β × Idx k → ℤ) : blockHadₗ k v = blockHad k v := rfl

end Block

end Hadamard

end LatticePrepro
