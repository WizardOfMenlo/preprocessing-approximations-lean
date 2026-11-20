import Mathlib

open Polynomial
variable {Ω : Type*} [Field Ω]

theorem LatticePrepro.exists_zmod_of_pow_eq {p : ℕ} [hp : Fact p.Prime] [Algebra (ZMod p) Ω] {c : Ω}
    (hc : c ^ p = c) : ∃ a : ZMod p, algebraMap (ZMod p) Ω a = c := by sorry
