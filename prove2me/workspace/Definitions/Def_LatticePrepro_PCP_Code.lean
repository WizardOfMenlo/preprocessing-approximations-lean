import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_PCP_Verifier

/-!
# The accepting-view code (Construction 6.2)

From a query-oblivious PCP `P`, an `F`-linear encoding map `E : F^m → F^B` on the space indexed by
the `m` accepting views, and an integer `g`, we build a fixed code and a target for every
instance. The encoding map `E` and the gap `g` are the paper's `ι` and `Γ`.

* Variables: one coordinate `v_{r,V,a}` for every accepting view, so `v : P.Views → F`.
* Constraints (`constraintMap`, `constraintRhs`): the system `G₀ · v = b_x` of equation (27), with
  one row for every random string `r` and every labeled predicate `V ∈ 𝒟_r`. Row `(r, V)` sums the
  variables of the views of `r` with predicate `V`, and `b_x` is `1` exactly on the rows
  `(r, V_{x,r})`. The map `G₀` does not depend on the instance.
* Restrictions (`restrict`): `v^{u,a}` keeps the variables of the views that answer `a` at the
  location `u`, and zeroes the others.
* The matrix `G₁` (`stackMap`): the paper stacks, for every queried location `u` and every
  `a ∈ Σ`, `d_u` copies of `v ↦ E(v^{u,a})`, where `d_u` is the number of pairs `(r, j)` with
  `u_{r,j} = u`. We index the copies by these pairs: the coordinates are
  `(r, j, a, b) ∈ {0,1}^ρ × [q] × Σ × [B]`, and the entry is `E(v^{u_{r,j},a})_b`. This is the
  paper's matrix up to the order of the rows, and it has `M₀ = |Σ| · Y` rows for
  `Y = B · 2^ρ · q` (`radius`).
* The code (`code`) is `(G₁ · ker G₀) × {0^H}` with `H = g · Y + 1`, and the target (`target`) is
  `(G₁ · v_x, 0^H)` for a solution `v_x` of `G₀ · v = b_x` if one exists, and `(0, 1^H)`
  otherwise.

The construction is for an arbitrary field `F`; the paper takes `F` finite. Computing the code
and the targets in polynomial time is not formalized.
-/

namespace LatticePrepro

/-- Padding a word by zeros on a second block of coordinates. -/
def padZero (F : Type) [Field F] (α β : Type) : (α → F) →ₗ[F] (α ⊕ β → F) where
  toFun c := Sum.elim c 0
  map_add' c c' := by funext i; cases i <;> simp
  map_smul' a c := by funext i; cases i <;> simp

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X) (F : Type) [Field F]

/-- The rows of the constraint system: pairs `(r, V)` of a random string and a labeled predicate
`V ∈ 𝒟_r`. -/
abbrev Row : Type := Σ r : P.Rand, P.Pred r

/-- The constraint map `G₀` (equation (27)): the row `(r, V)` is the sum of the variables
`v_{r,V,a}` over the accepting views `(V, a)` of `r` with predicate `V`. -/
def constraintMap : (P.Views → F) →ₗ[F] (P.Row → F) where
  toFun v := fun rV => ∑ w : P.View rV.1, if w.pred = rV.2 then v ⟨rV.1, w⟩ else 0
  map_add' v v' := by
    funext rV
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by split_ifs <;> simp
  map_smul' c v := by
    funext rV
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by split_ifs <;> simp

/-- The right-hand side `b_x` (equation (27)): `1` on the rows `(r, V_{x,r})` and `0` on the
others. -/
def constraintRhs (x : X) : P.Row → F :=
  fun rV => if rV.2 = P.verifier x rV.1 then 1 else 0

/-- The view `i` has answer `a` at the location `u`: `(u_{r,j}, a_j) = (u, a)` for some `j`. -/
def Hits (u : Fin P.ℓ) (a : P.Alphabet) (i : P.Views) : Prop :=
  ∃ j, P.query i.1 j = u ∧ i.2.ans j = a

instance (u : Fin P.ℓ) (a : P.Alphabet) (i : P.Views) : Decidable (P.Hits u a i) :=
  inferInstanceAs (Decidable (∃ j, P.query i.1 j = u ∧ i.2.ans j = a))

/-- The restriction `v ↦ v^{u,a}`: keep the variables of the views with answer `a` at `u`. -/
def restrict (u : Fin P.ℓ) (a : P.Alphabet) : (P.Views → F) →ₗ[F] (P.Views → F) where
  toFun v := fun i => if P.Hits u a i then v i else 0
  map_add' v v' := by funext i; by_cases h : P.Hits u a i <;> simp [h]
  map_smul' c v := by funext i; by_cases h : P.Hits u a i <;> simp [h]

/-- The coordinates of `G₁`: a query `(r, j)`, a symbol `a ∈ Σ` and a coordinate of the encoding
map. -/
abbrev Coord (B : ℕ) : Type := P.Rand × Fin P.q × P.Alphabet × Fin B

/-- The radius `Y = B · 2^ρ · q`. -/
def radius (B : ℕ) : ℕ := B * 2 ^ P.ρ * P.q

variable {F} {B : ℕ}

/-- The matrix `G₁`: the block of the query `(r, j)` and the symbol `a` is `E(v^{u_{r,j},a})`. -/
def stackMap (E : (P.Views → F) →ₗ[F] (Fin B → F)) : (P.Views → F) →ₗ[F] (P.Coord B → F) where
  toFun v := fun c => E (P.restrict F (P.query c.1 c.2.1) c.2.2.1 v) c.2.2.2
  map_add' v v' := by funext c; simp only [map_add, Pi.add_apply]
  map_smul' a v := by funext c; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- The code `(G₁ · ker G₀) × {0^H}` of Construction 6.2, with `H = g · Y + 1`. -/
def code (E : (P.Views → F) →ₗ[F] (Fin B → F)) (g : ℕ) :
    Submodule F (P.Coord B ⊕ Fin (g * P.radius B + 1) → F) :=
  (LinearMap.ker (P.constraintMap F)).map (padZero F _ _ ∘ₗ P.stackMap E)

open Classical in
/-- The target `y_x` of Construction 6.2: `(G₁ · v_x, 0^H)` for a solution `v_x` of
`G₀ · v = b_x` if there is one, and `(0, 1^H)` otherwise. -/
noncomputable def target (E : (P.Views → F) →ₗ[F] (Fin B → F)) (g : ℕ) (x : X) :
    P.Coord B ⊕ Fin (g * P.radius B + 1) → F :=
  if h : ∃ v, P.constraintMap F v = P.constraintRhs F x then
    Sum.elim (P.stackMap E h.choose) 0
  else Sum.elim 0 1

end ObliviousPCP

end LatticePrepro
