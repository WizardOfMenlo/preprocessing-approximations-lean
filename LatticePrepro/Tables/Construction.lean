import LatticePrepro.Moments.Representation
import LatticePrepro.Tables.Digits
import LatticePrepro.Tables.FieldSetup

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

section Linearity

variable {FS m}

lemma colSum_zero (η : Fin m → ℕ) (s : FS.𝕊) : colSum FS m (0 : Coord FS m → ZMod p) η s = 0 := by
  simp [colSum]

lemma colSum_add (y y' : Coord FS m → ZMod p) (η : Fin m → ℕ) (s : FS.𝕊) :
    colSum FS m (y + y') η s = colSum FS m y η s + colSum FS m y' η s := by
  simp [colSum, add_smul, Finset.sum_add_distrib]

lemma colSum_smul (c : ZMod p) (y : Coord FS m → ZMod p) (η : Fin m → ℕ) (s : FS.𝕊) :
    colSum FS m (c • y) η s = c • colSum FS m y η s := by
  simp [colSum, Finset.smul_sum, mul_smul]

lemma interp_zero (η : Fin m → ℕ) : interp FS m (0 : Coord FS m → ZMod p) η = 0 := by
  unfold interp
  have : (fun s => colSum FS m (0 : Coord FS m → ZMod p) η s) = 0 := by
    funext s; exact colSum_zero η s
  rw [this, map_zero]

lemma interp_add (y y' : Coord FS m → ZMod p) (η : Fin m → ℕ) :
    interp FS m (y + y') η = interp FS m y η + interp FS m y' η := by
  unfold interp
  have : (fun s => colSum FS m (y + y') η s) =
      (fun s => colSum FS m y η s) + (fun s => colSum FS m y' η s) := by
    funext s; exact colSum_add y y' η s
  rw [this, map_add]

variable {B}

lemma mom_zero (k : ℕ) : mom FS m B (0 : Coord FS m → ZMod p) k = 0 := by
  simp [mom, interp_zero]

lemma mom_add (y y' : Coord FS m → ZMod p) (k : ℕ) :
    mom FS m B (y + y') k = mom FS m B y k + mom FS m B y' k := by
  simp [mom, interp_add]

end Linearity

section Interpolation

variable {FS m}

/-- The interpolant takes the prescribed values at the nodes. -/
lemma eval_interp (y : Coord FS m → ZMod p) (η : Fin m → ℕ) (s : FS.𝕊) :
    eval s (interp FS m y η) = colSum FS m y η s := by
  unfold interp
  have := Lagrange.eval_interpolate_at_node (r := fun s => colSum FS m y η s)
    (Set.injOn_id _) (Finset.mem_univ s)
  simpa using this

lemma degree_interp_lt (y : Coord FS m → ZMod p) (η : Fin m → ℕ) :
    (interp FS m y η).degree < Fintype.card FS.𝕊 := by
  unfold interp
  have := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset FS.𝕊)) (v := id)
    (r := fun s => colSum FS m y η s) (Set.injOn_id _)
  simpa using this

/-- Interpolation uniqueness: a polynomial of degree `< q` with the right values is the
interpolant. -/
lemma interp_eq_of_eval_eq (y : Coord FS m → ZMod p) (η : Fin m → ℕ) {f : FS.𝕊[X]}
    (hf : f.degree < Fintype.card FS.𝕊) (h : ∀ s, eval s f = colSum FS m y η s) :
    interp FS m y η = f := by
  unfold interp
  exact (Lagrange.eq_interpolate_of_eval_eq (s := (Finset.univ : Finset FS.𝕊)) (v := id)
    (r := fun s => colSum FS m y η s) (Set.injOn_id _) (by simpa using hf)
    (fun s _ => by simpa using h s)).symm

lemma coeff_interp_eq_zero_of_card_le (y : Coord FS m → ZMod p) (η : Fin m → ℕ) {u : ℕ}
    (hu : Fintype.card FS.𝕊 ≤ u) : (interp FS m y η).coeff u = 0 :=
  coeff_eq_zero_of_degree_lt ((degree_interp_lt y η).trans_le (by exact_mod_cast hu))

end Interpolation

/-! ### Parameters -/

/-- The exponent index set `I = {0, …, 2p(B-1)}^m`. -/
abbrev IdxSet (p m B : ℕ) : Type := Fin m → Fin (2 * p * (B - 1) + 1)

/-- An index as an exponent vector. -/
def IdxSet.toNat {p m B : ℕ} (η : IdxSet p m B) : Fin m → ℕ := fun h => (η h).val

lemma IdxSet.toNat_le {p m B : ℕ} (η : IdxSet p m B) (h : Fin m) :
    η.toNat h ≤ 2 * p * (B - 1) := Nat.lt_succ_iff.mp (η h).isLt

/-- The degree bound `Δ = 2 p m (B - 1) (δ - 1)`. -/
def degBound (p m B δ : ℕ) : ℕ := 2 * p * m * (B - 1) * (δ - 1)

/-- The largest moment order carried by a table, `2ℓ - 2 = 2 p (B^m - 1)` where
`ℓ = p (B^m - 1) + 1` is the Hankel length. -/
def maxOrder (p m B : ℕ) : ℕ := 2 * p * (B ^ m - 1)

/-- Build an index from an exponent vector with small entries. -/
def IdxSet.ofNat {p m B : ℕ} (η : Fin m → ℕ) (hη : ∀ h, η h ≤ 2 * p * (B - 1)) : IdxSet p m B :=
  fun h => ⟨η h, Nat.lt_succ_of_le (hη h)⟩

@[simp] lemma IdxSet.toNat_ofNat {p m B : ℕ} (η : Fin m → ℕ) (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    (IdxSet.ofNat η hη).toNat = η := by
  funext h; rfl

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

/-- `K` has characteristic `p`. -/
lemma charP_K : CharP FS.K p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) FS.K).injective p

lemma constraintFun_zero : constraintFun FS m B (0 : Coord FS m → ZMod p) = 0 := by
  have := charP_K FS
  simp only [constraintFun, interp_zero, coeff_zero, ite_self, map_zero, mom_zero, sub_self,
    zero_pow (Fact.out : p.Prime).ne_zero]
  rfl

lemma constraintFun_add (y y' : Coord FS m → ZMod p) :
    constraintFun FS m B (y + y') = constraintFun FS m B y + constraintFun FS m B y' := by
  have := charP_K FS
  simp only [constraintFun, interp_add, coeff_add, map_add, mom_add, Prod.mk_add_mk,
    Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext ηu
    simp only [Pi.add_apply]
    split_ifs <;> simp
  · funext η
    simp only [Pi.add_apply]
    ring
  · funext k
    simp only [Pi.add_apply]
    split_ifs with h
    · rw [add_pow_char]
      ring
    · simp

/-- The constraint map as an `𝔽_p`-linear map. -/
noncomputable def constraintₗ : (Coord FS m → ZMod p) →ₗ[ZMod p] ConstrW FS m B :=
  AddMonoidHom.toZModLinearMap p
    { toFun := constraintFun FS m B
      map_zero' := constraintFun_zero FS m B
      map_add' := constraintFun_add FS m B }

@[simp] lemma constraintₗ_apply (y : Coord FS m → ZMod p) :
    constraintₗ FS m B y = constraintFun FS m B y := rfl

/-- The moment maps as `𝔽_p`-linear maps. -/
noncomputable def momₗ (k : ℕ) : (Coord FS m → ZMod p) →ₗ[ZMod p] FS.K :=
  AddMonoidHom.toZModLinearMap p
    { toFun := fun y => mom FS m B y k
      map_zero' := mom_zero k
      map_add' := fun y y' => mom_add y y' k }

@[simp] lemma momₗ_apply (k : ℕ) (y : Coord FS m → ZMod p) : momₗ FS m B k y = mom FS m B y k :=
  rfl

/-! ### Unpacking the constraints -/

section Unpack

variable {FS m B}

/-- Low-degree constraint: coefficients above `Δ` vanish. -/
lemma coeff_interp_eq_zero_of_constraint {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (η : IdxSet p m B) {u : ℕ} (hu : degBound p m B δ < u) :
    (interp FS m y η.toNat).coeff u = 0 := by
  by_cases hq : Fintype.card FS.𝕊 ≤ u
  · exact coeff_interp_eq_zero_of_card_le y _ hq
  · have hq' := not_le.mp hq
    have := congrFun (congrArg Prod.fst hy) (η, ⟨u, hq'⟩)
    simpa [constraintFun, hu] using this

/-- The interpolants of indexed exponent vectors have degree at most `Δ`. -/
lemma natDegree_interp_le_of_constraint {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (η : IdxSet p m B) :
    (interp FS m y η.toNat).natDegree ≤ degBound p m B δ :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hN => coeff_interp_eq_zero_of_constraint hy η hN

/-- Index-consistency constraint. -/
lemma aeval_interp_eq_mom_of_constraint {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (η : IdxSet p m B) :
    aeval FS.γ (interp FS m y η.toNat) = mom FS m B y (digitVal B η.toNat) := by
  have := congrFun (congrArg (fun w => w.2.1) hy) η
  simpa [constraintFun, sub_eq_zero] using this

/-- Frobenius constraint. -/
lemma mom_mul_eq_pow_of_constraint {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) {k : ℕ} (hk : p * k ≤ maxOrder p m B) :
    mom FS m B y (p * k) = (mom FS m B y k) ^ p := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hk' : k < maxOrder p m B + 1 := by
    have : k ≤ p * k := Nat.le_mul_of_pos_left k hp
    omega
  have := congrFun (congrArg (fun w => w.2.2) hy) ⟨k, hk'⟩
  simpa [constraintFun, hk, sub_eq_zero] using this

end Unpack

end ExplicitTables

end LatticePrepro
