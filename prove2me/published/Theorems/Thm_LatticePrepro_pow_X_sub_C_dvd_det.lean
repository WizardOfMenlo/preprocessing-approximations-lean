import Mathlib

open Polynomial Matrix
variable {𝕊 : Type*} [Field 𝕊] {n : Type*} [Fintype n] [DecidableEq n]

theorem LatticePrepro.pow_X_sub_C_dvd_det (M : Matrix n n 𝕊[X]) (s : 𝕊) :
    (X - C s) ^ (Fintype.card n - (M.map (eval s)).rank) ∣ M.det := by sorry
