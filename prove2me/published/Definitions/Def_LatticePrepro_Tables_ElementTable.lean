import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Construction

/-!
# Evaluation tables of field elements (Construction A.4, step 6; completeness in Theorem A.8)

For `α ∈ K` and `h < m`, let `ℓ_h ∈ 𝕊[X]` be the polynomial of degree `< δ` with
`ℓ_h(γ) = α^{B^h}`. The *element table* `ê_α` has a single `1` in every column `s`, at the label
`λ = (ℓ_0(s), …, ℓ_{m-1}(s))`. Its column sums are `∏_h ℓ_h(s)^{η_h}`, so its interpolants are the
low-degree polynomials `∏_h ℓ_h^{η_h}`, and its moments are `α^k`.
-/

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

/-- The polynomial `ℓ_h` with `ℓ_h(γ) = α^{B^h}` and degree `< δ`. -/
noncomputable def elemPoly (α : FS.K) (h : Fin m) : FS.𝕊[X] :=
  (FS.exists_aeval (α ^ B ^ (h : ℕ))).choose

/-- The product polynomial `∏_h ℓ_h^{η_h}`. -/
noncomputable def elemProd (α : FS.K) (η : Fin m → ℕ) : FS.𝕊[X] :=
  ∏ h, elemPoly FS m B α h ^ η h

variable {FS m B}

end ExplicitTables

end LatticePrepro
