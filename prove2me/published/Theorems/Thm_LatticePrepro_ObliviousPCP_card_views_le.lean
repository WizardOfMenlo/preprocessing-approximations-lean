import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier

open LatticePrepro
open LatticePrepro.ObliviousPCP
variable {X : Type} (P : ObliviousPCP X)

theorem LatticePrepro.ObliviousPCP.card_views_le {K : ℕ} (hK : ∀ r, Fintype.card (P.Pred r) ≤ K) :
    Fintype.card P.Views ≤ 2 ^ P.ρ * K * Fintype.card P.Alphabet ^ P.q := by sorry
