import LatticePrepro.Verifier.Gates

/-!
# Boolean circuits (Definitions 3.9–3.10)

A `BoolCircuit` has `n` input wires, `w` witness wires and `g` gates of fan-in two in topological
order: gate `k` reads two of the first `n + w + k` wires and writes wire `n + w + k`. A designated
gate is the output. Evaluation (`evalAux`) is defined by well-founded recursion on the wire index,
and the accepted language consists of the instances `x` for which some witness makes the output
wire `true`.

Reordering the wires as in Definition 3.10 (inputs, then the output wire, then the remaining
wires in order) turns a circuit into a `GateVerifier` with the same language
(`BoolCircuit.language_toGateVerifier`): the valid wire assignments of the gate verifier are
exactly the evaluations of the circuit.
-/

namespace LatticePrepro

/-- A Boolean circuit with gates of fan-in two in topological order. -/
structure BoolCircuit where
  /-- Number of input wires. -/
  n : ℕ
  /-- Number of witness wires. -/
  w : ℕ
  /-- Number of gates. -/
  g : ℕ
  /-- Gate `k` reads two of the first `n + w + k` wires. -/
  gateIn : (k : Fin g) → Fin (n + w + k.val) × Fin (n + w + k.val)
  /-- The Boolean function computed by gate `k`. -/
  gateFn : Fin g → Bool → Bool → Bool
  /-- The designated output gate. -/
  output : Fin g

namespace BoolCircuit

variable (C : BoolCircuit)

/-- The number of wires. -/
abbrev S : ℕ := C.n + C.w + C.g

/-- The index of the output wire. -/
def outW : ℕ := C.n + C.w + C.output.val

lemma outW_lt : C.outW < C.n + C.w + C.g := by
  unfold outW; have := C.output.isLt; omega

lemma n_le_outW : C.n ≤ C.outW := by unfold outW; omega

/-- Evaluation of the wire with index `i` on instance `x` and witness `wit`
(wires `≥ n + w + g` evaluate to `false`). -/
def evalAux (x : Fin C.n → Bool) (wit : Fin C.w → Bool) (i : ℕ) : Bool :=
  if h1 : i < C.n then x ⟨i, h1⟩
  else if h2 : i < C.n + C.w then wit ⟨i - C.n, by omega⟩
  else if h3 : i < C.n + C.w + C.g then
    C.gateFn ⟨i - (C.n + C.w), by omega⟩
      (evalAux x wit (C.gateIn ⟨i - (C.n + C.w), by omega⟩).1.val)
      (evalAux x wit (C.gateIn ⟨i - (C.n + C.w), by omega⟩).2.val)
  else false
termination_by i
decreasing_by
  · have h := (C.gateIn ⟨i - (C.n + C.w), by omega⟩).1.isLt
    simp only [Fin.val_mk] at h
    omega
  · have h := (C.gateIn ⟨i - (C.n + C.w), by omega⟩).2.isLt
    simp only [Fin.val_mk] at h
    omega

lemma evalAux_input (x : Fin C.n → Bool) (wit : Fin C.w → Bool) {i : ℕ} (h : i < C.n) :
    C.evalAux x wit i = x ⟨i, h⟩ := by
  rw [evalAux]; simp [h]

lemma evalAux_wit (x : Fin C.n → Bool) (wit : Fin C.w → Bool) {i : ℕ} (h1 : C.n ≤ i)
    (h2 : i < C.n + C.w) : C.evalAux x wit i = wit ⟨i - C.n, by omega⟩ := by
  rw [evalAux]
  have h1' : ¬ i < C.n := by omega
  simp [h1', h2]

lemma evalAux_gate (x : Fin C.n → Bool) (wit : Fin C.w → Bool) (k : Fin C.g) :
    C.evalAux x wit (C.n + C.w + k.val) =
      C.gateFn k (C.evalAux x wit (C.gateIn k).1.val) (C.evalAux x wit (C.gateIn k).2.val) := by
  obtain ⟨kv, hkv⟩ := k
  rw [evalAux]
  have h1 : ¬ (C.n + C.w + kv < C.n) := by omega
  have h2 : ¬ (C.n + C.w + kv < C.n + C.w) := by omega
  have h3 : C.n + C.w + kv < C.n + C.w + C.g := by omega
  simp only [h1, h2, h3, ↓reduceDIte]
  have e : (⟨C.n + C.w + kv - (C.n + C.w), by omega⟩ : Fin C.g) = ⟨kv, hkv⟩ := Fin.ext (by simp)
  exact congrArg (fun k : Fin C.g =>
    C.gateFn k (C.evalAux x wit (C.gateIn k).1.val) (C.evalAux x wit (C.gateIn k).2.val)) e

/-- The language of the circuit: instances with a witness making the output wire `true`. -/
def Language : Set (Fin C.n → Bool) := {x | ∃ wit, C.evalAux x wit C.outW = true}

/-! ### Reordering the wires -/

/-- The coordinate (in the order inputs, output, remaining wires) of a wire. -/
def coordOfNat (wi : ℕ) : ℕ :=
  if wi < C.n then wi else if wi = C.outW then C.n else if wi < C.outW then wi + 1 else wi

/-- The wire of a coordinate. -/
def wireOfNat (c : ℕ) : ℕ :=
  if c < C.n then c else if c = C.n then C.outW else if c - 1 < C.outW then c - 1 else c

lemma coordOfNat_lt {wi : ℕ} (_h : wi < C.n + C.w + C.g) : C.coordOfNat wi < C.n + C.w + C.g := by
  unfold coordOfNat
  have := C.outW_lt; have := C.n_le_outW
  split_ifs <;> omega

lemma wireOfNat_coordOfNat {wi : ℕ} (_h : wi < C.n + C.w + C.g) :
    C.wireOfNat (C.coordOfNat wi) = wi := by
  unfold coordOfNat wireOfNat
  have := C.outW_lt; have := C.n_le_outW
  split_ifs <;> omega

lemma coordOfNat_of_lt {wi : ℕ} (h : wi < C.n) : C.coordOfNat wi = wi := by
  simp [coordOfNat, h]

lemma coordOfNat_outW : C.coordOfNat C.outW = C.n := by
  have := C.n_le_outW
  simp [coordOfNat, show ¬ C.outW < C.n by omega]

lemma wireOfNat_of_lt {c : ℕ} (h : c < C.n) : C.wireOfNat c = c := by
  simp [wireOfNat, h]

lemma wireOfNat_n : C.wireOfNat C.n = C.outW := by
  simp [wireOfNat]

/-- The coordinate of a wire, as an element of `Fin S`. -/
def coordOf (wi : Fin C.S) : Fin C.S := ⟨C.coordOfNat wi, C.coordOfNat_lt wi.isLt⟩

/-- The wire written by gate `k`. -/
def gateWire (k : Fin C.g) : Fin C.S :=
  ⟨C.n + C.w + k.val, by show _ < C.n + C.w + C.g; have := k.isLt; omega⟩

/-- The first input wire of gate `k`. -/
def inWire1 (k : Fin C.g) : Fin C.S :=
  ⟨(C.gateIn k).1.val, by have := (C.gateIn k).1.isLt; have := k.isLt; show _ < C.n + C.w + C.g; omega⟩

/-- The second input wire of gate `k`. -/
def inWire2 (k : Fin C.g) : Fin C.S :=
  ⟨(C.gateIn k).2.val, by have := (C.gateIn k).2.isLt; have := k.isLt; show _ < C.n + C.w + C.g; omega⟩

/-- The gate verifier of a circuit (Definition 3.10): the coordinates list the inputs, then the
output wire, then the remaining wires in order. -/
abbrev toGateVerifier : GateVerifier where
  n := C.n
  S := C.S
  n_succ_le := by show C.n + 1 ≤ C.n + C.w + C.g; have := C.output.isLt; omega
  G := C.g
  gate := fun k =>
    (C.coordOf (C.gateWire k), C.coordOf (C.inWire1 k), C.coordOf (C.inWire2 k), C.gateFn k)

/-- Evaluations of the circuit, reordered, are valid assignments of the gate verifier. -/
lemma isValid_eval (x : Fin C.n → Bool) (wit : Fin C.w → Bool) :
    C.toGateVerifier.IsValid (fun c => C.evalAux x wit (C.wireOfNat c)) := by
  intro k
  simp only [GateVerifier.out, GateVerifier.in1, GateVerifier.in2, GateVerifier.fn, toGateVerifier,
    coordOf]
  rw [C.wireOfNat_coordOfNat (C.gateWire k).isLt, C.wireOfNat_coordOfNat (C.inWire1 k).isLt,
    C.wireOfNat_coordOfNat (C.inWire2 k).isLt]
  exact C.evalAux_gate x wit k

lemma hasPrefix_eval (x : Fin C.n → Bool) (wit : Fin C.w → Bool) (hout : C.evalAux x wit C.outW = true) :
    C.toGateVerifier.HasPrefix x (fun c => C.evalAux x wit (C.wireOfNat c)) := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [GateVerifier.inputWire, toGateVerifier]
    rw [C.wireOfNat_of_lt i.isLt, C.evalAux_input x wit i.isLt]
  · simp only [GateVerifier.outputWire, toGateVerifier]
    rw [C.wireOfNat_n]
    exact hout

/-- The witness read off a wire assignment of the gate verifier. -/
def witOf (z : Fin C.S → Bool) (j : Fin C.w) : Bool :=
  z ⟨C.coordOfNat (C.n + j.val), C.coordOfNat_lt (by have := j.isLt; omega)⟩

/-- A valid assignment of the gate verifier with prefix `(x, _)` is the evaluation of the
circuit on `x` and the witness it contains. -/
lemma evalAux_eq_of_isValid {x : Fin C.n → Bool} {z : Fin C.S → Bool}
    (hz : C.toGateVerifier.IsValid z) (hpre : ∀ i, z (C.toGateVerifier.inputWire i) = x i) :
    ∀ wi (hwi : wi < C.n + C.w + C.g),
      C.evalAux x (C.witOf z) wi = z ⟨C.coordOfNat wi, C.coordOfNat_lt hwi⟩ := by
  intro wi
  induction wi using Nat.strong_induction_on with
  | _ wi ih =>
    intro hwi
    by_cases h1 : wi < C.n
    · rw [C.evalAux_input x _ h1, ← hpre ⟨wi, h1⟩]
      congr 1
      exact Fin.ext (by simp [GateVerifier.inputWire, toGateVerifier, C.coordOfNat_of_lt h1])
    by_cases h2 : wi < C.n + C.w
    · rw [C.evalAux_wit x _ (by omega) h2]
      unfold witOf
      congr 1
      exact Fin.ext (by simp; congr 1; omega)
    · obtain ⟨k, hk⟩ : ∃ k : Fin C.g, wi = C.n + C.w + k.val :=
        ⟨⟨wi - (C.n + C.w), by omega⟩, by simp; omega⟩
      subst hk
      rw [C.evalAux_gate x _ k]
      have e1 := (C.gateIn k).1.isLt
      have e2 := (C.gateIn k).2.isLt
      rw [ih _ e1 (by have := k.isLt; omega), ih _ e2 (by have := k.isLt; omega)]
      exact (hz k).symm

/-- The wire reordering preserves the language. -/
theorem language_toGateVerifier : C.toGateVerifier.Language = C.Language := by
  ext x
  simp only [GateVerifier.Language, Language, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz, hpre⟩
    refine ⟨C.witOf z, ?_⟩
    rw [C.evalAux_eq_of_isValid hz hpre.1 C.outW C.outW_lt]
    have := hpre.2
    simp only [GateVerifier.outputWire, toGateVerifier] at this
    rw [← this]
    congr 1
    exact Fin.ext (by simp [C.coordOfNat_outW])
  · rintro ⟨wit, hout⟩
    exact ⟨fun c => C.evalAux x wit (C.wireOfNat c), C.isValid_eval x wit,
      C.hasPrefix_eval x wit hout⟩

end BoolCircuit

end LatticePrepro
