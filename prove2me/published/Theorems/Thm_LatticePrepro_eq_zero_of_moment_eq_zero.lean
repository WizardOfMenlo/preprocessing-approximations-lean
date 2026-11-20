import Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic

open LatticePrepro
open Finsupp
variable {Ω : Type*} [Field Ω]

theorem LatticePrepro.eq_zero_of_moment_eq_zero (g : Ω →₀ Ω) {t : ℕ} (hs : g.support.card ≤ t)
    (h : ∀ k < t, moment g k = 0) : g = 0 := by sorry
