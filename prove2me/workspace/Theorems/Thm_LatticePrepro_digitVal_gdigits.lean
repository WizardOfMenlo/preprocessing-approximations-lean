import Mathlib
import Definitions.Def_LatticePrepro_Tables_Digits

open LatticePrepro

theorem LatticePrepro.digitVal_gdigits {B m : ℕ} (hB : 2 ≤ B) (hm : 1 ≤ m) (k : ℕ) :
    digitVal B (gdigits B m k) = k := by sorry
