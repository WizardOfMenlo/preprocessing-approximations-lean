import Mathlib

/-!
# Quadratic verifiers and encodings

The moment reduction only uses a verifier through a system of homogeneous quadratic equations
over `𝔽_p` in the coordinates `(z_0, z_1, …, z_S)` with `z_0 = 1` (Claim 3.11 of the paper
produces such a system from a Boolean circuit with fan-in-two gates).

We therefore abstract a verifier as a `QuadraticVerifier`: it has `S` assignment coordinates
(indexed by `Fin (S+1)`, where index `0` is the constant coordinate), `n` input coordinates
(indices `1, …, n`), the output coordinate `n + 1`, and `G` quadratic *gate equations*.

An assignment is *valid* if all gate equations vanish, and *accepting on `x`* if it is valid,
Boolean, and has prefix `(x, 1)`. The language of the verifier is the set of instances with
an accepting assignment (Definitions 3.9 and 3.10).

We also define *encoding tuples* `E = (E_1, …, E_S)` of `𝔽_p`-linearly independent elements of
a field `K`, the encoding `enc z = ∑ E_i z_i` of an assignment, and the instance encoding
`θ_x = enc (x, 1, 0, …, 0)`.
-/

namespace LatticePrepro

/-- A quadratic verifier over `ZMod p` (cf. Definitions 3.9, 3.10 and Claim 3.11). -/
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

/-- Assignments with a constant coordinate: `z 0` is intended to be `1`. -/
abbrev Assignment := Fin (V.S + 1) → ZMod p

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

/-- Accepting computation on `x` (Definition 3.10). -/
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

lemma assignOf_zero (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) : V.assignOf x u 0 = 1 := by
  simp [assignOf]

lemma assignOf_apply_of_le (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) {i : Fin (V.S + 1)}
    (h0 : i.val ≠ 0) (hn : i.val ≤ V.n) :
    V.assignOf x u i = if x ⟨i.val - 1, by omega⟩ then 1 else 0 := by
  simp only [assignOf, h0, hn, ↓reduceDIte]

lemma assignOf_apply_of_eq (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) {i : Fin (V.S + 1)}
    (h : i.val = V.n + 1) : V.assignOf x u i = 1 := by
  simp [assignOf, h]

lemma assignOf_apply_of_lt (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) {i : Fin (V.S + 1)}
    (h : V.n + 1 < i.val) : V.assignOf x u i = u ⟨i, h⟩ := by
  have h0 : i.val ≠ 0 := by omega
  have hn : ¬ i.val ≤ V.n := by omega
  have hout : i.val ≠ V.n + 1 := by omega
  simp only [assignOf, h0, hn, hout, ↓reduceDIte]

lemma assignOf_inputIdx (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) (i : Fin V.n) :
    V.assignOf x u (V.inputIdx i) = if x i then 1 else 0 := by
  rw [V.assignOf_apply_of_le x u (i := V.inputIdx i) (by simp [inputIdx]) (by simp [inputIdx])]
  simp [inputIdx]

lemma assignOf_outputIdx (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) :
    V.assignOf x u V.outputIdx = 1 :=
  V.assignOf_apply_of_eq x u rfl

lemma assignOf_aux (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) (i : V.AuxIdx) :
    V.assignOf x u i.1 = u i :=
  V.assignOf_apply_of_lt x u i.2

lemma assignOf_hasPrefix (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) :
    V.HasPrefix x (V.assignOf x u) :=
  ⟨V.assignOf_inputIdx x u, V.assignOf_outputIdx x u⟩

lemma assignOf_isBoolean (x : Fin V.n → Bool) {u : V.AuxIdx → ZMod p}
    (hu : ∀ i, u i = 0 ∨ u i = 1) : V.IsBooleanAssignment (V.assignOf x u) := by
  refine ⟨V.assignOf_zero x u, fun i => ?_⟩
  by_cases h0 : i.val = 0
  · rw [show i = 0 from Fin.ext h0, V.assignOf_zero]; exact Or.inr rfl
  by_cases hn : i.val ≤ V.n
  · rw [V.assignOf_apply_of_le x u h0 hn]; split_ifs <;> simp
  by_cases hout : i.val = V.n + 1
  · rw [V.assignOf_apply_of_eq x u hout]; exact Or.inr rfl
  · rw [V.assignOf_apply_of_lt x u (by omega)]; exact hu _

/-- Two assignments agreeing with prefix `(x,1)` and on the auxiliary coordinates are equal. -/
lemma eq_assignOf {x : Fin V.n → Bool} {z : Fin (V.S + 1) → ZMod p} (h0 : z 0 = 1)
    (hpre : V.HasPrefix x z) : z = V.assignOf x (fun i => z i.1) := by
  funext i
  by_cases hi : i.val = 0
  · rw [show i = 0 from Fin.ext hi, V.assignOf_zero]; exact h0
  by_cases hn : i.val ≤ V.n
  · rw [V.assignOf_apply_of_le x _ hi hn]
    have := hpre.1 ⟨i.val - 1, by omega⟩
    rw [show V.inputIdx ⟨i.val - 1, by omega⟩ = i from Fin.ext (by simp [inputIdx]; omega)] at this
    exact this
  by_cases hout : i.val = V.n + 1
  · rw [V.assignOf_apply_of_eq x _ hout, show i = V.outputIdx from Fin.ext hout]; exact hpre.2
  · rw [V.assignOf_apply_of_lt x _ (by omega)]

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

lemma enc_eq_sum_succ (z : Fin (S + 1) → ZMod p) :
    ε.enc z = ∑ i : Fin S, z i.succ • ε.E i.succ := by
  rw [enc, Fin.sum_univ_succ, ε.E_zero, smul_zero, zero_add]

lemma enc_add (z z' : Fin (S + 1) → ZMod p) : ε.enc (z + z') = ε.enc z + ε.enc z' := by
  simp [enc, add_smul, Finset.sum_add_distrib]

lemma enc_sub (z z' : Fin (S + 1) → ZMod p) : ε.enc (z - z') = ε.enc z - ε.enc z' := by
  simp [enc, sub_smul, Finset.sum_sub_distrib]

lemma enc_zero : ε.enc 0 = 0 := by simp [enc]

/-- A vanishing combination `∑ c_i E_i = 0` with `c_0` arbitrary forces `c_i = 0` for `i ≥ 1`. -/
lemma eq_zero_of_sum_smul_eq_zero {c : Fin (S + 1) → ZMod p} (h : ∑ i, c i • ε.E i = 0)
    (i : Fin (S + 1)) (hi : i ≠ 0) : c i = 0 := by
  rw [Fin.sum_univ_succ, ε.E_zero, smul_zero, zero_add] at h
  obtain ⟨j, rfl⟩ : ∃ j : Fin S, i = j.succ := ⟨i.pred hi, (Fin.succ_pred i hi).symm⟩
  exact (Fintype.linearIndependent_iff.mp ε.linearIndependent) (fun j => c j.succ) h j

/-- Encodings are injective on assignments with equal constant coordinate. -/
lemma enc_injective {z z' : Fin (S + 1) → ZMod p} (h0 : z 0 = z' 0) (h : ε.enc z = ε.enc z') :
    z = z' := by
  funext i
  by_cases hi : i = 0
  · subst hi; exact h0
  · have : ∑ j, (z - z') j • ε.E j = 0 := by
      rw [← enc, enc_sub, h, sub_self]
    have := ε.eq_zero_of_sum_smul_eq_zero this i hi
    simpa [sub_eq_zero] using this

/-- The `K`-linear independence of the `E_i` transfers along an injective algebra map. -/
lemma linearIndependent_map {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω]
    [IsScalarTower (ZMod p) K Ω] :
    LinearIndependent (ZMod p) (fun i : Fin S => algebraMap K Ω (ε.E i.succ)) := by
  have := ε.linearIndependent.map' (IsScalarTower.toAlgHom (ZMod p) K Ω).toLinearMap
    (LinearMap.ker_eq_bot.mpr (algebraMap K Ω).injective)
  exact this

end EncodingTuple

namespace QuadraticVerifier

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  (V : QuadraticVerifier p) (ε : EncodingTuple p K V.S)

/-- The instance encoding `θ_x = enc (x, 1, 0, …, 0)`. -/
def instanceEnc (x : Fin V.n → Bool) : K := ε.enc (V.assignOf x 0)

/-- The encoding of `assignOf x u` is `θ_x` plus the auxiliary contribution. -/
lemma enc_assignOf (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) :
    ε.enc (V.assignOf x u) = V.instanceEnc ε x + ∑ i : V.AuxIdx, u i • ε.E i.1 := by
  classical
  unfold instanceEnc EncodingTuple.enc
  -- extend `u` by zero to all coordinates
  let u' : Fin (V.S + 1) → ZMod p := fun i => if h : V.n + 1 < i.val then u ⟨i, h⟩ else 0
  have key : ∀ i : Fin (V.S + 1), V.assignOf x u i • ε.E i =
      V.assignOf x 0 i • ε.E i + u' i • ε.E i := by
    intro i
    by_cases h : V.n + 1 < i.val
    · simp only [u', h, ↓reduceDIte]
      rw [V.assignOf_apply_of_lt x u h, V.assignOf_apply_of_lt x 0 h]
      simp
    · simp only [u', h, ↓reduceDIte, zero_smul, add_zero]
      by_cases hi : i.val = 0
      · rw [show i = 0 from Fin.ext hi, V.assignOf_zero, V.assignOf_zero]
      by_cases hn : i.val ≤ V.n
      · rw [V.assignOf_apply_of_le x u hi hn, V.assignOf_apply_of_le x 0 hi hn]
      · rw [V.assignOf_apply_of_eq x u (by omega), V.assignOf_apply_of_eq x 0 (by omega)]
  simp_rw [key]
  rw [Finset.sum_add_distrib]
  congr 1
  have h1 : ∑ i : V.AuxIdx, u i • ε.E i.1 = ∑ i : V.AuxIdx, u' i.1 • ε.E i.1 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [u', i.2]
  rw [h1, ← Finset.sum_subtype (Finset.univ.filter fun i : Fin (V.S + 1) => V.n + 1 < i.val)
    (by simp) (fun i => u' i • ε.E i), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : V.n + 1 < i.val
  · simp [h]
  · simp [u', h]

end QuadraticVerifier

end LatticePrepro
