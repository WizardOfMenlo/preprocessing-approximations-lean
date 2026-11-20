import Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Tables_Hankel

open LatticePrepro
open Polynomial

theorem LatticePrepro.hankel_reconstruction {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω]
    [Algebra (ZMod p) Ω] [IsAlgClosed Ω] {r : ℕ} (hr : 2 ≤ r) (y : ℕ → Ω)
    (hfrob : ∀ k, p * k ≤ 2 * hankelLen p r - 2 → y (p * k) = y k ^ p)
    {t : ℕ} (ht : t < r)
    (hdep : ∃ c : Fin (t + 1) → Ω, c ≠ 0 ∧
      ∀ i : Fin (hankelLen p r), ∑ j, c j * y (i.val + j.val) = 0) :
    ∃ f : Ω →₀ ZMod p, f.support.card ≤ t ∧ ∀ k < hankelLen p r, y k = moment f k := by sorry
