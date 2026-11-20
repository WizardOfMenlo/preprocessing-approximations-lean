import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Conversions_ConstructionA

/-! Further definitions from `LatticePrepro/Conversions/ConstructionA.lean`, continuing `Def_LatticePrepro_Conversions_ConstructionA`. -/

namespace LatticePrepro

open Finset

variable {p : ℕ} [Fact p.Prime] {M : Type*}

/-- Coordinatewise reduction modulo `p` as a `ℤ`-linear map. -/
def redMod (p : ℕ) (M : Type*) : (M → ℤ) →ₗ[ℤ] (M → ZMod p) :=
  LinearMap.pi fun i => (Int.castAddHom (ZMod p)).toIntLinearMap ∘ₗ LinearMap.proj i

@[simp] lemma redMod_apply (v : M → ℤ) (i : M) : redMod p M v i = (v i : ZMod p) := rfl

/-- The Construction A lattice `Λ_𝒞 = {v : v mod p ∈ 𝒞}`. -/
def constructionA (C : Submodule (ZMod p) (M → ZMod p)) : Submodule ℤ (M → ℤ) :=
  (C.restrictScalars ℤ).comap (redMod p M)

@[simp] lemma redMod_liftZMod (y : M → ZMod p) : redMod p M (liftZMod y) = y := by
  funext i
  simp [liftZMod]

end LatticePrepro
