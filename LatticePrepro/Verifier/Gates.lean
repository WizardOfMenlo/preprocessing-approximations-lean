import LatticePrepro.Verifier.Quadratic

/-!
# Gate verifiers and quadratic gate equations (Definitions 3.9–3.10, Claim 3.11)

A *gate verifier* is a system of Boolean constraints `z_o = f(z_l, z_{l'})` with fan-in two on
wires `Fin S`: wires `0, …, n-1` carry the instance, wire `n` is the output wire, and the remaining
wires carry the witness and the gate outputs. An assignment is *valid* if every gate constraint
holds, and the language consists of the instances `x` with a valid assignment with prefix
`(x, true)`.

Following Claim 3.11, each gate function `f : Bool → Bool → Bool` is interpolated by the
multilinear polynomial `a + b u + c v + d u v` with integer coefficients, and the gate constraint
becomes the homogeneous quadratic equation
`z_0 z_o - a z_0 z_0 - b z_0 z_l - c z_0 z_{l'} - d z_l z_{l'} = 0`
over `𝔽_p`, where `z_0 = 1` is the constant coordinate. The resulting `QuadraticVerifier` has the
same language (`GateVerifier.language_toQuadratic`).
-/

namespace LatticePrepro

/-! ### Quadratic forms given by coefficient tensors -/

section QuadForm

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The quadratic form `∑ i j, T i j * z i * z j` of a coefficient tensor. -/
def quadForm (T : Fin m → Fin m → R) (z : Fin m → R) : R := ∑ i, ∑ j, T i j * (z i * z j)

/-- The coefficient tensor of the single monomial `c · z_{i₀} z_{j₀}`. -/
def deltaTensor [DecidableEq (Fin m)] (i₀ j₀ : Fin m) (c : R) : Fin m → Fin m → R :=
  fun i j => if i = i₀ ∧ j = j₀ then c else 0

lemma quadForm_sub (T T' : Fin m → Fin m → R) (z : Fin m → R) :
    quadForm (T - T') z = quadForm T z - quadForm T' z := by
  simp [quadForm, sub_mul, Finset.sum_sub_distrib]

lemma quadForm_deltaTensor (i₀ j₀ : Fin m) (c : R) (z : Fin m → R) :
    quadForm (deltaTensor i₀ j₀ c) z = c * (z i₀ * z j₀) := by
  unfold quadForm deltaTensor
  rw [Finset.sum_eq_single i₀]
  · rw [Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (Finset.mem_univ _) h

end QuadForm

/-- A verifier given by Boolean gates of fan-in two on wires `Fin S` (Definition 3.9):
wires `0, …, n - 1` are the inputs, wire `n` is the output, and each gate
`(o, l, l', f)` imposes `z o = f (z l) (z l')`. -/
structure GateVerifier where
  /-- Instance length. -/
  n : ℕ
  /-- Number of wires. -/
  S : ℕ
  /-- The input wires and the output wire fit. -/
  n_succ_le : n + 1 ≤ S
  /-- Number of gates. -/
  G : ℕ
  /-- The gates `(output wire, input wire 1, input wire 2, gate function)`. -/
  gate : Fin G → Fin S × Fin S × Fin S × (Bool → Bool → Bool)

namespace GateVerifier

variable (W : GateVerifier)

/-- The output wire of a gate. -/
def out (b : Fin W.G) : Fin W.S := (W.gate b).1
/-- The first input wire of a gate. -/
def in1 (b : Fin W.G) : Fin W.S := (W.gate b).2.1
/-- The second input wire of a gate. -/
def in2 (b : Fin W.G) : Fin W.S := (W.gate b).2.2.1
/-- The Boolean function of a gate. -/
def fn (b : Fin W.G) : Bool → Bool → Bool := (W.gate b).2.2.2

/-- An assignment to the wires is valid if every gate is evaluated correctly. -/
def IsValid (z : Fin W.S → Bool) : Prop :=
  ∀ b, z (W.out b) = W.fn b (z (W.in1 b)) (z (W.in2 b))

/-- The `i`-th input wire. -/
def inputWire (i : Fin W.n) : Fin W.S := ⟨i.val, by have := W.n_succ_le; omega⟩

/-- The output wire `n`. -/
def outputWire : Fin W.S := ⟨W.n, by have := W.n_succ_le; omega⟩

/-- The assignment has prefix `(x, true)`. -/
def HasPrefix (x : Fin W.n → Bool) (z : Fin W.S → Bool) : Prop :=
  (∀ i, z (W.inputWire i) = x i) ∧ z W.outputWire = true

/-- The language of the gate verifier (Definition 3.9). -/
def Language : Set (Fin W.n → Bool) := {x | ∃ z, W.IsValid z ∧ W.HasPrefix x z}

/-! ### Multilinear interpolation of a gate function -/

/-- Constant coefficient `a = f 0 0`. -/
def c00 (f : Bool → Bool → Bool) : ℤ := (f false false).toNat
/-- Coefficient of `u`: `b = f 1 0 - f 0 0`. -/
def c10 (f : Bool → Bool → Bool) : ℤ := (f true false).toNat - (f false false).toNat
/-- Coefficient of `v`: `c = f 0 1 - f 0 0`. -/
def c01 (f : Bool → Bool → Bool) : ℤ := (f false true).toNat - (f false false).toNat
/-- Coefficient of `u v`: `d = f 1 1 - f 1 0 - f 0 1 + f 0 0`. -/
def c11 (f : Bool → Bool → Bool) : ℤ :=
  (f true true).toNat - (f true false).toNat - (f false true).toNat + (f false false).toNat

/-- The interpolation identity `f u v = a + b u + c v + d u v` on Boolean inputs. -/
lemma toNat_eq_interp (f : Bool → Bool → Bool) (u v : Bool) :
    ((f u v).toNat : ℤ) =
      c00 f + c10 f * u.toNat + c01 f * v.toNat + c11 f * (u.toNat * v.toNat) := by
  cases u <;> cases v <;>
    simp only [Bool.toNat_true, Bool.toNat_false, c00, c10, c01, c11, Nat.cast_one,
      Nat.cast_zero] <;> ring

/-! ### The quadratic verifier of a gate verifier -/

/-- The quadratic verifier of Claim 3.11: the gate `(o, l, l', f)` becomes the equation
`z_0 z_o - a z_0 z_0 - b z_0 z_l - c z_0 z_{l'} - d z_l z_{l'} = 0`. -/
abbrev toQuadratic (p : ℕ) : QuadraticVerifier p where
  n := W.n
  S := W.S
  n_succ_le := W.n_succ_le
  G := W.G
  coeff := fun b =>
    deltaTensor 0 (W.out b).succ 1 - deltaTensor 0 0 ((c00 (W.fn b) : ℤ) : ZMod p) -
      deltaTensor 0 (W.in1 b).succ ((c10 (W.fn b) : ℤ) : ZMod p) -
      deltaTensor 0 (W.in2 b).succ ((c01 (W.fn b) : ℤ) : ZMod p) -
      deltaTensor (W.in1 b).succ (W.in2 b).succ ((c11 (W.fn b) : ℤ) : ZMod p)

variable (p : ℕ)

@[simp] lemma toQuadratic_n : (W.toQuadratic p).n = W.n := rfl
@[simp] lemma toQuadratic_S : (W.toQuadratic p).S = W.S := rfl
@[simp] lemma toQuadratic_G : (W.toQuadratic p).G = W.G := rfl

lemma gateEq_toQuadratic (b : Fin W.G) (z : Fin (W.S + 1) → ZMod p) :
    (W.toQuadratic p).gateEq b z =
      z 0 * z (W.out b).succ - ((c00 (W.fn b) : ℤ) : ZMod p) * (z 0 * z 0) -
        ((c10 (W.fn b) : ℤ) : ZMod p) * (z 0 * z (W.in1 b).succ) -
        ((c01 (W.fn b) : ℤ) : ZMod p) * (z 0 * z (W.in2 b).succ) -
        ((c11 (W.fn b) : ℤ) : ZMod p) * (z (W.in1 b).succ * z (W.in2 b).succ) := by
  show quadForm _ z = _
  simp only [quadForm_sub, quadForm_deltaTensor, one_mul]

/-- The `𝔽_p`-assignment `(1, z)` of a Boolean wire assignment `z`. -/
def lift (z : Fin W.S → Bool) : Fin (W.S + 1) → ZMod p :=
  Fin.cons 1 fun i => ((z i).toNat : ZMod p)

@[simp] lemma lift_zero (z : Fin W.S → Bool) : W.lift p z 0 = 1 := by
  simp [lift]

@[simp] lemma lift_succ (z : Fin W.S → Bool) (i : Fin W.S) :
    W.lift p z i.succ = ((z i).toNat : ZMod p) := by
  simp [lift]

/-- On lifted assignments, the gate equation evaluates to `z_o - f(z_l, z_{l'})`. -/
lemma gateEq_lift (b : Fin W.G) (z : Fin W.S → Bool) :
    (W.toQuadratic p).gateEq b (W.lift p z) =
      ((((z (W.out b)).toNat : ℤ) - ((W.fn b (z (W.in1 b)) (z (W.in2 b))).toNat : ℤ) : ℤ) :
        ZMod p) := by
  rw [gateEq_toQuadratic, toNat_eq_interp (W.fn b) (z (W.in1 b)) (z (W.in2 b))]
  simp only [lift_zero, lift_succ]
  push_cast
  ring

lemma inputIdx_toQuadratic (i : Fin W.n) :
    (W.toQuadratic p).inputIdx i = (W.inputWire i).succ := rfl

lemma outputIdx_toQuadratic : (W.toQuadratic p).outputIdx = W.outputWire.succ := rfl

variable [Fact p.Prime]

lemma toNat_sub_toNat_cast_eq_zero_iff (u v : Bool) :
    ((((u.toNat : ℤ) - (v.toNat : ℤ) : ℤ) : ZMod p) = 0) ↔ u = v := by
  cases u <;> cases v <;> simp

lemma isValid_lift_iff (z : Fin W.S → Bool) :
    (W.toQuadratic p).IsValid (W.lift p z) ↔ W.IsValid z := by
  unfold QuadraticVerifier.IsValid IsValid
  refine forall_congr' fun b => ?_
  rw [gateEq_lift, toNat_sub_toNat_cast_eq_zero_iff]

lemma toNat_cast_eq_ite_iff (u v : Bool) :
    ((u.toNat : ZMod p) = if v then 1 else 0) ↔ u = v := by
  cases u <;> cases v <;> simp

lemma toNat_cast_eq_one_iff (u : Bool) : ((u.toNat : ZMod p) = 1) ↔ u = true := by
  cases u <;> simp

lemma hasPrefix_lift_iff (x : Fin W.n → Bool) (z : Fin W.S → Bool) :
    (W.toQuadratic p).HasPrefix x (W.lift p z) ↔ W.HasPrefix x z := by
  unfold QuadraticVerifier.HasPrefix HasPrefix
  rw [outputIdx_toQuadratic, lift_succ, toNat_cast_eq_one_iff]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  rw [inputIdx_toQuadratic, lift_succ, toNat_cast_eq_ite_iff]

lemma isBoolean_lift (z : Fin W.S → Bool) :
    (W.toQuadratic p).IsBooleanAssignment (W.lift p z) := by
  refine ⟨W.lift_zero p z, fun i => ?_⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rw [lift_succ]; cases z j <;> simp

/-- The Boolean wire assignment underlying an `𝔽_p`-assignment. -/
def toBits (z' : Fin (W.S + 1) → ZMod p) : Fin W.S → Bool := fun i => decide (z' i.succ = 1)

/-- A Boolean `𝔽_p`-assignment is the lift of its underlying bits. -/
lemma eq_lift_toBits {z' : Fin (W.S + 1) → ZMod p}
    (hz : (W.toQuadratic p).IsBooleanAssignment z') : z' = W.lift p (W.toBits p z') := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [lift_zero]; exact hz.1
  · rw [lift_succ]
    unfold toBits
    rcases hz.2 j.succ with h | h
    · rw [h]
      have : (0 : ZMod p) ≠ 1 := zero_ne_one
      simp [this]
    · rw [h]; simp

/-- **Claim 3.11**: the quadratic verifier accepts the same language. -/
theorem language_toQuadratic : (W.toQuadratic p).Language = W.Language := by
  ext x
  simp only [QuadraticVerifier.Language, Language, Set.mem_ofPred_eq, QuadraticVerifier.IsAccepting]
  constructor
  · rintro ⟨z', hbool, hvalid, hpre⟩
    rw [W.eq_lift_toBits p hbool] at hvalid hpre
    exact ⟨W.toBits p z', (W.isValid_lift_iff p _).mp hvalid, (W.hasPrefix_lift_iff p x _).mp hpre⟩
  · rintro ⟨z, hvalid, hpre⟩
    exact ⟨W.lift p z, W.isBoolean_lift p z, (W.isValid_lift_iff p z).mpr hvalid,
      (W.hasPrefix_lift_iff p x z).mpr hpre⟩

end GateVerifier

end LatticePrepro
