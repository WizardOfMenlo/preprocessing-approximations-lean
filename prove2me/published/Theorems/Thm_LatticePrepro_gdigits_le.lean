import Mathlib
import Definitions.Def_LatticePrepro_Tables_Digits

open LatticePrepro

theorem LatticePrepro.gdigits_le {B m J k : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) (hJ : 1 ≤ J)
    (hk : k ≤ J * (B ^ m - 1)) (h : Fin m) : gdigits B m k h ≤ J * (B - 1) := by sorry
