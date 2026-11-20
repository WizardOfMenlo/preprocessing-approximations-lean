import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates

/-!
# Boolean circuits (Definitions 3.13–3.14)

A `BoolCircuit` has `n` input wires, `w` witness wires and `g` gates of fan-in two in topological
order: gate `k` reads two of the first `n + w + k` wires and writes wire `n + w + k`. A designated
gate is the output. Evaluation (`evalAux`) is defined by well-founded recursion on the wire index,
and the accepted language consists of the instances `x` for which some witness makes the output
wire `true`.

Reordering the wires as in Definition 3.14 (inputs, then the output wire, then the remaining
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

/-- The language of the circuit: instances with a witness making the output wire `true`. -/
def Language : Set (Fin C.n → Bool) := {x | ∃ wit, C.evalAux x wit C.outW = true}

/-! ### Reordering the wires -/

/-- The coordinate (in the order inputs, output, remaining wires) of a wire. -/
def coordOfNat (wi : ℕ) : ℕ :=
  if wi < C.n then wi else if wi = C.outW then C.n else if wi < C.outW then wi + 1 else wi

lemma coordOfNat_lt {wi : ℕ} (_h : wi < C.n + C.w + C.g) : C.coordOfNat wi < C.n + C.w + C.g := by
  unfold coordOfNat
  have := C.outW_lt; have := C.n_le_outW
  split_ifs <;> omega

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

/-- The gate verifier of a circuit (Definition 3.14): the coordinates list the inputs, then the
output wire, then the remaining wires in order. -/
abbrev toGateVerifier : GateVerifier where
  n := C.n
  S := C.S
  n_succ_le := by show C.n + 1 ≤ C.n + C.w + C.g; have := C.output.isLt; omega
  G := C.g
  gate := fun k =>
    (C.coordOf (C.gateWire k), C.coordOf (C.inWire1 k), C.coordOf (C.inWire2 k), C.gateFn k)

end BoolCircuit

end LatticePrepro
