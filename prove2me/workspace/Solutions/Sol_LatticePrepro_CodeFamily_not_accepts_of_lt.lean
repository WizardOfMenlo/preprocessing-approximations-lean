import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Conversions_SearchTest

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.CodeFamily end LatticePrepro.CodeFamily

namespace LatticePrepro

namespace CodeFamily

variable {F : Type} [Field F] {X : Type}

lemma codeDist_le [DecidableEq F] {M : Type} [Fintype M] (y : M → F) (C : Submodule F (M → F))
    {c : M → F} (hc : c ∈ C) : codeDist y C ≤ hammingDist y c :=
  Nat.sInf_le ⟨c, hc, rfl⟩

end CodeFamily

end LatticePrepro

namespace LatticePrepro

namespace CodeFamily

variable {F : Type} [Field F] [DecidableEq F] {X : Type} (C : CodeFamily F X)

/-- **Lemma 5.2 for codes, NO instances**: if `dist(t_x, 𝒞) > g · R`, every vector is rejected. -/
private theorem not_accepts_of_lt {g R : ℕ} {x : X} (hx : g * R < codeDist (C.target x) C.code)
    (c : C.M → F) : ¬ C.Accepts g R x c := by
  rintro ⟨hc, hd⟩
  exact absurd (codeDist_le (C.target x) C.code hc) (by omega)

end CodeFamily

end LatticePrepro

open LatticePrepro
open LatticePrepro.CodeFamily
variable {F : Type} [Field F] [DecidableEq F] {X : Type} (C : CodeFamily F X)
theorem solution {g R : ℕ} {x : X} (hx : g * R < codeDist (C.target x) C.code)
    (c : C.M → F) : ¬ C.Accepts g R x c :=
  @LatticePrepro.CodeFamily.not_accepts_of_lt F _ _ X C g R x hx c
