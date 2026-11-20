import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Construction

/-!
# Soundness of the explicit tables: the polynomial matrix (Definition A.5, Lemma A.6)

For a table `y` satisfying the constraints, the *polynomial matrix* `Hmat y` has entries
`P^y_{digits(h) + digits(h')} ∈ 𝕊[X]` (`0 ≤ h, h' < ℓ`, `ℓ = p (B^m - 1) + 1`). We show:

* its entries have degree `≤ Δ` (low-degree constraints);
* `Hmat y (s) = E · diag(y(·, s)) · Eᵀ`, so `∑_s rank Hmat y (s) ≤ wt(y)`;
* `Hmat y (γ)` is the Hankel matrix `(M̂_{h+h'}(y))` (index-consistency constraints);
* hence, by `card_mul_rank_eval_le`, the Hankel matrix has rank `ρ` with `(q - Δ) ρ ≤ wt(y)`,
  and its first `ρ + 1` columns are linearly dependent.
-/

namespace LatticePrepro

open Polynomial Matrix

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

/-- The Hankel length `ℓ = p (B^m - 1) + 1` (this is `hankelLen p (B^m)`). -/
def hLen (p m B : ℕ) : ℕ := p * (B ^ m - 1) + 1

variable {FS m B}

end ExplicitTables

end LatticePrepro
