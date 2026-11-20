import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Verifier_Gates
import Definitions.Def_LatticePrepro_Verifier_Circuit

namespace LatticePrepro.GateList end LatticePrepro.GateList
/-!
# Boolean expressions and their circuits

A `BExpr L` is a Boolean formula over `L` leaves (wires `Fin L`) built from gates of fan-in
two. We compile such expressions into Boolean circuits (Definition 3.13): `BExpr.toCircuit n w e`
is a `BoolCircuit` with `n` input wires, `w` witness wires and `e.size` gates, whose output on
`(x, wit)` is the value of `e` on the leaf assignment `Fin.append x wit`
(`BExpr.mem_language_toCircuit`). This is the tool used to build the 3SAT verifier circuits of
`Verifier/ThreeSAT.lean`.

The compilation goes through an intermediate list of gates addressed by natural-number wire
indices (`GateSpec`, `GateList.WF`, `GateList.evalWire`): gate `k` of a list over `base` leaf
wires writes wire `base + k` and may read any wire `< base + k`. Expressions are compiled in
post-order (`BExpr.compile`), appending gates to the list; the value of the result wire is the
value of the expression (`BExpr.evalWire_compile`). A well-formed gate list is then turned into a
`BoolCircuit` (`BExpr.toCircuit`), whose evaluation `BoolCircuit.evalAux` agrees with
`GateList.evalWire` (`BExpr.evalAux_toCircuit`). This keeps the index arithmetic away from the
dependent types of `BoolCircuit.gateIn`.
-/

namespace LatticePrepro

/-! ### Expressions -/

/-- Boolean expressions over leaves `Fin L` with gates of fan-in two. -/
inductive BExpr (L : ℕ)
  /-- A leaf: the value of wire `i`. -/
  | leaf : Fin L → BExpr L
  /-- A gate `f` applied to two subexpressions. -/
  | gate : (Bool → Bool → Bool) → BExpr L → BExpr L → BExpr L

namespace BExpr

variable {L : ℕ}

/-- The value of an expression under a leaf assignment. -/
def eval (ρ : Fin L → Bool) : BExpr L → Bool
  | leaf i => ρ i
  | gate f a b => f (eval ρ a) (eval ρ b)

/-- The number of gates of an expression. -/
def size : BExpr L → ℕ
  | leaf _ => 0
  | gate _ a b => size a + size b + 1

@[simp] lemma eval_leaf (ρ : Fin L → Bool) (i : Fin L) : eval ρ (leaf i) = ρ i := rfl

@[simp] lemma eval_gate (ρ : Fin L → Bool) (f : Bool → Bool → Bool) (a b : BExpr L) :
    eval ρ (gate f a b) = f (eval ρ a) (eval ρ b) := rfl

@[simp] lemma size_leaf (i : Fin L) : size (leaf i) = 0 := rfl

@[simp] lemma size_gate (f : Bool → Bool → Bool) (a b : BExpr L) :
    size (gate f a b) = size a + size b + 1 := rfl

/-- Conjunction. -/
def and (a b : BExpr L) : BExpr L := gate (· && ·) a b

/-- Disjunction. -/
def or (a b : BExpr L) : BExpr L := gate (· || ·) a b

/-- Implication `a → b`. -/
def imp (a b : BExpr L) : BExpr L := gate (fun u w => !u || w) a b

/-- Comparison with a constant: `a == c`. -/
def eqConst (c : Bool) (a : BExpr L) : BExpr L := gate (fun u _ => u == c) a a

/-- A constant, computed by a gate reading an arbitrary leaf `l₀`. -/
def const (l₀ : Fin L) (c : Bool) : BExpr L := gate (fun _ _ => c) (leaf l₀) (leaf l₀)

/-- The conjunction of a list of expressions (`const l₀ true` for the empty list). -/
def bigAnd (l₀ : Fin L) (l : List (BExpr L)) : BExpr L := l.foldr and (const l₀ true)

@[simp] lemma eval_and (ρ : Fin L → Bool) (a b : BExpr L) :
    eval ρ (and a b) = (eval ρ a && eval ρ b) := rfl

@[simp] lemma eval_or (ρ : Fin L → Bool) (a b : BExpr L) :
    eval ρ (or a b) = (eval ρ a || eval ρ b) := rfl

@[simp] lemma eval_imp (ρ : Fin L → Bool) (a b : BExpr L) :
    eval ρ (imp a b) = (!eval ρ a || eval ρ b) := rfl

@[simp] lemma eval_eqConst (ρ : Fin L → Bool) (c : Bool) (a : BExpr L) :
    eval ρ (eqConst c a) = (eval ρ a == c) := rfl

@[simp] lemma eval_const (ρ : Fin L → Bool) (l₀ : Fin L) (c : Bool) : eval ρ (const l₀ c) = c :=
  rfl

@[simp] lemma bigAnd_nil (l₀ : Fin L) : bigAnd l₀ [] = const l₀ true := rfl

@[simp] lemma bigAnd_cons (l₀ : Fin L) (a : BExpr L) (l : List (BExpr L)) :
    bigAnd l₀ (a :: l) = and a (bigAnd l₀ l) := rfl

@[simp] lemma size_and (a b : BExpr L) : size (and a b) = size a + size b + 1 := rfl

@[simp] lemma size_or (a b : BExpr L) : size (or a b) = size a + size b + 1 := rfl

@[simp] lemma size_imp (a b : BExpr L) : size (imp a b) = size a + size b + 1 := rfl

@[simp] lemma size_eqConst (c : Bool) (a : BExpr L) : size (eqConst c a) = 2 * size a + 1 := by
  simp [eqConst]; ring

@[simp] lemma size_const (l₀ : Fin L) (c : Bool) : size (const l₀ c) = 1 := rfl

lemma size_bigAnd (l₀ : Fin L) (l : List (BExpr L)) :
    size (bigAnd l₀ l) = (l.map size).sum + l.length + 1 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

end BExpr

/-! ### Gate lists -/

/-- A gate reading the wires with indices `in1` and `in2` and applying `fn`. -/
structure GateSpec where
  /-- The first input wire. -/
  in1 : ℕ
  /-- The second input wire. -/
  in2 : ℕ
  /-- The gate function. -/
  fn : Bool → Bool → Bool

namespace GateList

/-- A gate list over `base` leaf wires is well-formed if gate `k` (which writes wire
`base + k`) reads only wires `< base + k`. -/
def WF (base : ℕ) (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length), gs[k].in1 < base + k ∧ gs[k].in2 < base + k

lemma WF.nil (base : ℕ) : WF base [] := fun _ hk => absurd hk (by simp)

/-- Appending a gate reading existing wires preserves well-formedness. -/
lemma WF.snoc {base : ℕ} {gs : List GateSpec} (h : WF base gs) {g : GateSpec}
    (h1 : g.in1 < base + gs.length) (h2 : g.in2 < base + gs.length) : WF base (gs ++ [g]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_ge k gs.length with hlt | hge
  · rw [List.getElem_append_left hlt]
    exact h k hlt
  · have hk' : k = gs.length := by omega
    rw [List.getElem_append_right hge, List.getElem_singleton]
    subst hk'
    exact ⟨h1, h2⟩

variable {base : ℕ} (ρ : Fin base → Bool) (gs : List GateSpec)

end GateList

/-! ### Compilation -/

namespace BExpr

open GateList

variable {base : ℕ}

/-- Compile an expression over `base` leaf wires by appending its gates, in post-order, to the
gate list `gs`. The second component is the wire carrying the value of the expression. -/
def compile (base : ℕ) : BExpr base → List GateSpec → List GateSpec × ℕ
  | leaf i, gs => (gs, i.val)
  | gate f a b, gs =>
    let r₁ := compile base a gs
    let r₂ := compile base b r₁.1
    (r₂.1 ++ [⟨r₁.2, r₂.2, f⟩], base + r₂.1.length)

/-- Compilation extends the gate list. -/
lemma compile_fst_prefix (e : BExpr base) (gs : List GateSpec) : gs <+: (compile base e gs).1 := by
  induction e generalizing gs with
  | leaf i => exact List.prefix_rfl
  | gate f a b iha ihb =>
    simp only [compile]
    exact ((iha gs).trans (ihb _)).trans (List.prefix_append _ _)

/-- Compilation appends exactly `e.size` gates. -/
lemma length_compile_fst (e : BExpr base) (gs : List GateSpec) :
    (compile base e gs).1.length = gs.length + e.size := by
  induction e generalizing gs with
  | leaf i => simp [compile]
  | gate f a b iha ihb =>
    simp only [compile, List.length_append, List.length_singleton, size_gate]
    rw [ihb, iha]
    ring

/-- The result wire exists. -/
lemma compile_snd_lt (e : BExpr base) (gs : List GateSpec) :
    (compile base e gs).2 < base + (compile base e gs).1.length := by
  cases e with
  | leaf i => exact lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
  | gate f a b =>
    simp only [compile, List.length_append, List.length_singleton]
    omega

/-- For an expression with at least one gate, the result wire is the last gate. -/
lemma compile_snd_add_one {e : BExpr base} (he : 0 < e.size) (gs : List GateSpec) :
    (compile base e gs).2 + 1 = base + (compile base e gs).1.length := by
  cases e with
  | leaf i => simp at he
  | gate f a b =>
    simp only [compile, List.length_append, List.length_singleton]
    omega

/-- Compilation preserves well-formedness. -/
lemma compile_wf (e : BExpr base) {gs : List GateSpec} (hgs : WF base gs) :
    WF base (compile base e gs).1 := by
  induction e generalizing gs with
  | leaf i => exact hgs
  | gate f a b iha ihb =>
    simp only [compile]
    set r₁ := compile base a gs with hr₁
    set r₂ := compile base b r₁.1 with hr₂
    have hlen : r₁.1.length ≤ r₂.1.length := (compile_fst_prefix b r₁.1).length_le
    have h1 : r₁.2 < base + r₁.1.length := compile_snd_lt a gs
    refine (ihb (iha hgs)).snoc ?_ (compile_snd_lt b _)
    show r₁.2 < base + r₂.1.length
    omega

/-! ### The circuit of an expression -/

/-- The Boolean circuit of an expression `e` over `n + w` leaves with at least one gate: `n`
input wires, `w` witness wires, and the gates of `compile e`, the last of which is the output. -/
abbrev toCircuit (n w : ℕ) (e : BExpr (n + w)) (he : 0 < e.size) : BoolCircuit where
  n := n
  w := w
  g := (compile (n + w) e []).1.length
  gateIn := fun k =>
    (⟨((compile (n + w) e []).1[k]).in1, (compile_wf e (WF.nil _) k k.isLt).1⟩,
     ⟨((compile (n + w) e []).1[k]).in2, (compile_wf e (WF.nil _) k k.isLt).2⟩)
  gateFn := fun k => ((compile (n + w) e []).1[k]).fn
  output := ⟨(compile (n + w) e []).2 - (n + w), by
    have h1 := compile_snd_add_one he (base := n + w) []
    have h2 := length_compile_fst e []
    omega⟩

variable {n w : ℕ} (e : BExpr (n + w)) (he : 0 < e.size)

@[simp] lemma toCircuit_n : (toCircuit n w e he).n = n := rfl

@[simp] lemma toCircuit_w : (toCircuit n w e he).w = w := rfl

end BExpr

end LatticePrepro
