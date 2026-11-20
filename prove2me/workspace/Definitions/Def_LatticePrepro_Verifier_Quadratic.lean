import Mathlib

/-!
# Quadratic verifiers and encodings

The moment reduction only uses a verifier through a system of homogeneous quadratic equations
over `𝔽_p` in the coordinates `(z_0, z_1, …, z_S)` with `z_0 = 1` (Claim 3.15 of the paper
produces such a system from a Boolean circuit with fan-in-two gates).

We therefore abstract a verifier as a `QuadraticVerifier`: it has `S` assignment coordinates
(indexed by `Fin (S+1)`, where index `0` is the constant coordinate), `n` input coordinates
(indices `1, …, n`), the output coordinate `n + 1`, and `G` quadratic *gate equations*.

An assignment is *valid* if all gate equations vanish, and *accepting on `x`* if it is valid,
Boolean, and has prefix `(x, 1)`. The language of the verifier is the set of instances with
an accepting assignment (Definitions 3.13 and 3.14).

We also define *encoding tuples* `E = (E_1, …, E_S)` of `𝔽_p`-linearly independent elements of
a field `K`, the encoding `enc z = ∑ E_i z_i` of an assignment, and the instance encoding
`θ_x = enc (x, 1, 0, …, 0)`.
-/

namespace LatticePrepro

/-- A quadratic verifier over `ZMod p` (cf. Definitions 3.13, 3.14 and Claim 3.15). -/
structure QuadraticVerifier (p : ℕ) where
  /-- Instance length. -/
  n : ℕ
  /-- Number of assignment coordinates (excluding the constant coordinate `0`). -/
  S : ℕ
  /-- The prefix `(x, 1)` fits into the assignment. -/
  n_succ_le : n + 1 ≤ S
  /-- Number of gate equations. -/
  G : ℕ
  /-- Coefficients `c^{(b)}_{(i,j)}` of the gate equations. -/
  coeff : Fin G → Fin (S + 1) → Fin (S + 1) → ZMod p

namespace QuadraticVerifier

variable {p : ℕ} (V : QuadraticVerifier p)

/-- The value `Q_b(z) = ∑ c_{ij} z_i z_j` of the `b`-th gate equation. -/
def gateEq (b : Fin V.G) (z : Fin (V.S + 1) → ZMod p) : ZMod p :=
  ∑ i, ∑ j, V.coeff b i j * (z i * z j)

/-- An assignment is valid if all gate equations vanish. -/
def IsValid (z : Fin (V.S + 1) → ZMod p) : Prop := ∀ b, V.gateEq b z = 0

/-- Boolean assignments with constant coordinate `1`. -/
def IsBooleanAssignment (z : Fin (V.S + 1) → ZMod p) : Prop :=
  z 0 = 1 ∧ ∀ i, z i = 0 ∨ z i = 1

/-- The index of the `i`-th input coordinate (`1 ≤ i + 1 ≤ n`). -/
def inputIdx (i : Fin V.n) : Fin (V.S + 1) := ⟨i.val + 1, by have := V.n_succ_le; omega⟩

/-- The index `n + 1` of the output coordinate. -/
def outputIdx : Fin (V.S + 1) := ⟨V.n + 1, by have := V.n_succ_le; omega⟩

/-- Indices `i > n + 1` of the remaining (witness and gate) coordinates. -/
abbrev AuxIdx : Type := {i : Fin (V.S + 1) // V.n + 1 < i.val}

/-- The assignment has prefix `(x, 1)`. -/
def HasPrefix (x : Fin V.n → Bool) (z : Fin (V.S + 1) → ZMod p) : Prop :=
  (∀ i, z (V.inputIdx i) = if x i then 1 else 0) ∧ z V.outputIdx = 1

/-- Accepting computation on `x` (Definition 3.14). -/
def IsAccepting (x : Fin V.n → Bool) (z : Fin (V.S + 1) → ZMod p) : Prop :=
  V.IsBooleanAssignment z ∧ V.IsValid z ∧ V.HasPrefix x z

/-- The language accepted by the verifier. -/
def Language : Set (Fin V.n → Bool) := {x | ∃ z, V.IsAccepting x z}

/-- The canonical assignment with prefix `(x, 1)` and values `u` on the auxiliary coordinates. -/
def assignOf (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) : Fin (V.S + 1) → ZMod p :=
  fun i =>
    if h0 : i.val = 0 then 1
    else if hn : i.val ≤ V.n then (if x ⟨i.val - 1, by omega⟩ then 1 else 0)
    else if hout : i.val = V.n + 1 then 1
    else u ⟨i, by omega⟩

end QuadraticVerifier

/-- An encoding tuple: `𝔽_p`-linearly independent elements `E_1, …, E_S` of `K`, indexed by
`Fin (S+1)` with the convention `E_0 = 0`. -/
structure EncodingTuple (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K]
    (S : ℕ) where
  /-- The elements `E_0 = 0, E_1, …, E_S`. -/
  E : Fin (S + 1) → K
  E_zero : E 0 = 0
  linearIndependent : LinearIndependent (ZMod p) (fun i : Fin S => E i.succ)

namespace EncodingTuple

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {S : ℕ}
  (ε : EncodingTuple p K S)

/-- The encoding `∑ i, z_i • E_i` of an assignment. -/
def enc (z : Fin (S + 1) → ZMod p) : K := ∑ i, z i • ε.E i

end EncodingTuple

namespace QuadraticVerifier

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  (V : QuadraticVerifier p) (ε : EncodingTuple p K V.S)

/-- The instance encoding `θ_x = enc (x, 1, 0, …, 0)`. -/
def instanceEnc (x : Fin V.n → Bool) : K := ε.enc (V.assignOf x 0)

end QuadraticVerifier

end LatticePrepro
