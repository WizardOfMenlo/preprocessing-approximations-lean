import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup

/-!
# Polynomial evaluation tables: the construction (Construction A.4)

Fix a field setup `FS` (sample field `𝕊` of size `q`, moment field `K = 𝕊(γ)` of degree `δ`)
and integers `m ≥ 1`, `B ≥ 2`. An evaluation table is a vector `y : (Fin m → 𝕊) × 𝕊 → 𝔽_p`;
its coordinates `(λ, s)` are partitioned into the `q` columns `s ∈ 𝕊`, each of size `q^m`.

* `colSum y η s = ∑ λ, y (λ, s) • λ^η` is the weighted column sum for the exponent vector `η`.
* `interp y η ∈ 𝕊[X]` is the polynomial of degree `< q` interpolating `s ↦ colSum y η s`.
* `mom y k = (interp y (gdigits B m k)) (γ)` is the `k`-th moment map.
* `constraintFun y` collects the low-degree, index-consistency and Frobenius constraints.

All of these are `𝔽_p`-linear in `y`.
-/

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

/-- Coordinates of an evaluation table: a label `λ ∈ 𝕊^m` and a column `s ∈ 𝕊`. -/
abbrev Coord : Type := (Fin m → FS.𝕊) × FS.𝕊

/-- The weighted column sum `∑ λ, y (λ, s) • λ^η`. -/
def colSum (y : Coord FS m → ZMod p) (η : Fin m → ℕ) (s : FS.𝕊) : FS.𝕊 :=
  ∑ lam : Fin m → FS.𝕊, y (lam, s) • ∏ h, lam h ^ η h

/-- The interpolating polynomial of the column sums (degree `< q`). -/
noncomputable def interp (y : Coord FS m → ZMod p) (η : Fin m → ℕ) : FS.𝕊[X] :=
  Lagrange.interpolate (Finset.univ : Finset FS.𝕊) id (fun s => colSum FS m y η s)

/-- The `k`-th moment map `M̂_k(y) = P^y_{digits(k)}(γ)`. -/
noncomputable def mom (y : Coord FS m → ZMod p) (k : ℕ) : FS.K :=
  aeval FS.γ (interp FS m y (gdigits B m k))

/-! ### Parameters -/

/-- The exponent index set `I = {0, …, 2p(B-1)}^m`. -/
abbrev IdxSet (p m B : ℕ) : Type := Fin m → Fin (2 * p * (B - 1) + 1)

/-- An index as an exponent vector. -/
def IdxSet.toNat {p m B : ℕ} (η : IdxSet p m B) : Fin m → ℕ := fun h => (η h).val

/-- The degree bound `Δ = 2 p m (B - 1) (δ - 1)`. -/
def degBound (p m B δ : ℕ) : ℕ := 2 * p * m * (B - 1) * (δ - 1)

/-- The largest moment order carried by a table, `2ℓ - 2 = 2 p (B^m - 1)` where
`ℓ = p (B^m - 1) + 1` is the Hankel length. -/
def maxOrder (p m B : ℕ) : ℕ := 2 * p * (B ^ m - 1)

/-- The codomain of the constraint map: low-degree rows, index-consistency rows and
Frobenius rows. -/
abbrev ConstrW : Type :=
  (IdxSet p m B × Fin (Fintype.card FS.𝕊) → FS.𝕊) × (IdxSet p m B → FS.K) ×
    (Fin (maxOrder p m B + 1) → FS.K)

/-- The evaluation table constraints (Construction A.4, step 5), as a function of `y`. -/
noncomputable def constraintFun (y : Coord FS m → ZMod p) : ConstrW FS m B :=
  (fun ηu => if degBound p m B δ < ηu.2.val then (interp FS m y ηu.1.toNat).coeff ηu.2.val else 0,
   fun η => aeval FS.γ (interp FS m y η.toNat) - mom FS m B y (digitVal B η.toNat),
   fun k => if p * k.val ≤ maxOrder p m B then
     mom FS m B y (p * k.val) - (mom FS m B y k.val) ^ p else 0)

/-! ### Unpacking the constraints -/

end ExplicitTables

end LatticePrepro
