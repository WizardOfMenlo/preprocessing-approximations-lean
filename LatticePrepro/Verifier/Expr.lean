import LatticePrepro.Verifier.Circuit

/-!
# Boolean expressions and their circuits

A `BExpr L` is a Boolean formula over `L` leaves (wires `Fin L`) built from gates of fan-in
two. We compile such expressions into Boolean circuits (Definition 3.9): `BExpr.toCircuit n w e`
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

/-- The disjunction of a list of expressions (`const l₀ false` for the empty list). -/
def bigOr (l₀ : Fin L) (l : List (BExpr L)) : BExpr L := l.foldr or (const l₀ false)

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

@[simp] lemma bigOr_nil (l₀ : Fin L) : bigOr l₀ [] = const l₀ false := rfl

@[simp] lemma bigOr_cons (l₀ : Fin L) (a : BExpr L) (l : List (BExpr L)) :
    bigOr l₀ (a :: l) = or a (bigOr l₀ l) := rfl

lemma eval_bigAnd (ρ : Fin L → Bool) (l₀ : Fin L) (l : List (BExpr L)) :
    eval ρ (bigAnd l₀ l) = l.all (eval ρ) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma eval_bigOr (ρ : Fin L → Bool) (l₀ : Fin L) (l : List (BExpr L)) :
    eval ρ (bigOr l₀ l) = l.any (eval ρ) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

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

lemma size_bigOr (l₀ : Fin L) (l : List (BExpr L)) :
    size (bigOr l₀ l) = (l.map size).sum + l.length + 1 := by
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

/-- The value of wire `i`: leaves `i < base` are read from `ρ`, wire `base + k` carries gate `k`
applied to the values of its input wires, and wires beyond the list (or gates reading a wire
that is not earlier) evaluate to `false`. -/
def evalWire (base : ℕ) (ρ : Fin base → Bool) (gs : List GateSpec) (i : ℕ) : Bool :=
  if h : i < base then ρ ⟨i, h⟩
  else
    match gs[i - base]? with
    | none => false
    | some g =>
      if _h : g.in1 < i ∧ g.in2 < i then g.fn (evalWire base ρ gs g.in1) (evalWire base ρ gs g.in2)
      else false
termination_by i
decreasing_by
  · exact _h.1
  · exact _h.2

variable {base : ℕ} (ρ : Fin base → Bool) (gs : List GateSpec)

lemma evalWire_of_lt {i : ℕ} (h : i < base) : evalWire base ρ gs i = ρ ⟨i, h⟩ := by
  rw [evalWire]
  simp [h]

lemma evalWire_of_none {i : ℕ} (h : base ≤ i) (hg : gs[i - base]? = none) :
    evalWire base ρ gs i = false := by
  rw [evalWire]
  simp [not_lt.mpr h, hg]

lemma evalWire_of_some {i : ℕ} (h : base ≤ i) {g : GateSpec} (hg : gs[i - base]? = some g) :
    evalWire base ρ gs i =
      if g.in1 < i ∧ g.in2 < i then g.fn (evalWire base ρ gs g.in1) (evalWire base ρ gs g.in2)
      else false := by
  conv_lhs => rw [evalWire]
  simp only [not_lt.mpr h, ↓reduceDIte, hg]
  split_ifs <;> rfl

/-- Appending gates does not change the values of the existing wires. -/
lemma evalWire_append (gs' : List GateSpec) {i : ℕ} (hi : i < base + gs.length) :
    evalWire base ρ (gs ++ gs') i = evalWire base ρ gs i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h : i < base
    · rw [evalWire_of_lt ρ _ h, evalWire_of_lt ρ _ h]
    · have h' : base ≤ i := not_lt.mp h
      have hget : (gs ++ gs')[i - base]? = gs[i - base]? :=
        List.getElem?_append_left (by omega)
      rcases hg : gs[i - base]? with _ | g
      · rw [evalWire_of_none ρ _ h' (hget.trans hg), evalWire_of_none ρ _ h' hg]
      · rw [evalWire_of_some ρ _ h' (hget.trans hg), evalWire_of_some ρ _ h' hg]
        split_ifs with h12
        · rw [ih _ h12.1 (by omega), ih _ h12.2 (by omega)]
        · rfl

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

/-- The result wire of a compiled expression carries its value. -/
lemma evalWire_compile (ρ : Fin base → Bool) (e : BExpr base) (gs : List GateSpec) :
    evalWire base ρ (compile base e gs).1 (compile base e gs).2 = e.eval ρ := by
  induction e generalizing gs with
  | leaf i => rw [compile, evalWire_of_lt ρ _ i.isLt, eval_leaf]
  | gate f a b iha ihb =>
    simp only [compile, eval_gate]
    set r₁ := compile base a gs with hr₁
    set r₂ := compile base b r₁.1 with hr₂
    have hlen : r₁.1.length ≤ r₂.1.length := (compile_fst_prefix b r₁.1).length_le
    have h1' : r₁.2 < base + r₁.1.length := compile_snd_lt a gs
    have h1 : r₁.2 < base + r₂.1.length := by omega
    have h2 : r₂.2 < base + r₂.1.length := compile_snd_lt b r₁.1
    have hget : (r₂.1 ++ [(⟨r₁.2, r₂.2, f⟩ : GateSpec)])[base + r₂.1.length - base]? =
        some ⟨r₁.2, r₂.2, f⟩ := by
      rw [Nat.add_sub_cancel_left, List.getElem?_append_right le_rfl, Nat.sub_self]
      rfl
    rw [evalWire_of_some ρ _ (Nat.le_add_right _ _) hget]
    simp only [h1, h2, and_self, ↓reduceIte]
    rw [evalWire_append ρ _ _ h1, evalWire_append ρ _ _ h2, hr₂, ihb]
    obtain ⟨t, ht⟩ := compile_fst_prefix b r₁.1
    rw [← ht, evalWire_append ρ _ _ (compile_snd_lt a gs), iha]

/-! ### The circuit of an expression -/

/-- `Fin.append` on an index below `n`. -/
lemma append_mk_of_lt {n w : ℕ} (x : Fin n → Bool) (wit : Fin w → Bool) {i : ℕ} (h : i < n)
    (h' : i < n + w) : Fin.append x wit ⟨i, h'⟩ = x ⟨i, h⟩ :=
  Fin.append_left x wit ⟨i, h⟩

/-- `Fin.append` on an index at least `n`. -/
lemma append_mk_of_le {n w : ℕ} (x : Fin n → Bool) (wit : Fin w → Bool) {i : ℕ} (h : n ≤ i)
    (h' : i < n + w) : Fin.append x wit ⟨i, h'⟩ = wit ⟨i - n, Nat.sub_lt_left_of_lt_add h h'⟩ := by
  have := Fin.append_right x wit ⟨i - n, Nat.sub_lt_left_of_lt_add h h'⟩
  rw [← this]
  congr 1
  ext
  simp only [Fin.natAdd_mk]
  omega

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

lemma toCircuit_g : (toCircuit n w e he).g = e.size := by
  show (compile (n + w) e []).1.length = e.size
  rw [length_compile_fst, List.length_nil, zero_add]

/-- The number of wires of the circuit of an expression. -/
lemma toCircuit_S : (toCircuit n w e he).S = n + w + e.size := by
  show n + w + (toCircuit n w e he).g = _
  rw [toCircuit_g]

lemma toCircuit_outW : (toCircuit n w e he).outW = (compile (n + w) e []).2 := by
  show n + w + ((compile (n + w) e []).2 - (n + w)) = _
  have h1 := compile_snd_add_one he (base := n + w) []
  have h2 := length_compile_fst e []
  omega

/-- The circuit of an expression evaluates its wires as the compiled gate list does. -/
lemma evalAux_toCircuit (x : Fin n → Bool) (wit : Fin w → Bool) (i : ℕ) :
    (toCircuit n w e he).evalAux x wit i =
      evalWire (n + w) (Fin.append x wit) (compile (n + w) e []).1 i := by
  set gs := (compile (n + w) e []).1 with hgs
  have hwf : WF (n + w) gs := compile_wf e (WF.nil _)
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · rw [(toCircuit n w e he).evalAux_input x wit h1, evalWire_of_lt _ _ (by omega),
        append_mk_of_lt x wit h1]
    by_cases h2 : i < n + w
    · rw [(toCircuit n w e he).evalAux_wit x wit (not_lt.mp h1) h2, evalWire_of_lt _ _ h2,
        append_mk_of_le x wit (not_lt.mp h1)]
    by_cases h3 : i < n + w + gs.length
    · obtain ⟨k, rfl⟩ : ∃ k : Fin (toCircuit n w e he).g, i = n + w + k.val :=
        ⟨⟨i - (n + w), by show i - (n + w) < gs.length; omega⟩, by simp; omega⟩
      rw [(toCircuit n w e he).evalAux_gate x wit k]
      have hget : gs[n + w + k.val - (n + w)]? = some gs[k.val] := by
        rw [Nat.add_sub_cancel_left]
        exact List.getElem?_eq_getElem k.isLt
      rw [evalWire_of_some _ _ (Nat.le_add_right _ _) hget]
      obtain ⟨hk1, hk2⟩ := hwf k.val k.isLt
      simp only [hk1, hk2, and_self, ↓reduceIte]
      rw [← ih _ hk1, ← ih _ hk2]
      rfl
    · rw [evalWire_of_none _ _ (by omega) (List.getElem?_eq_none (by omega))]
      have h1' : ¬ i < (toCircuit n w e he).n := h1
      have h2' : ¬ i < (toCircuit n w e he).n + (toCircuit n w e he).w := h2
      have h3' : ¬ i < (toCircuit n w e he).n + (toCircuit n w e he).w +
          (toCircuit n w e he).g := h3
      rw [BoolCircuit.evalAux, dite_eq_right h1', dite_eq_right h2', dite_eq_right h3']

/-- **The language of the circuit of an expression**: the instances `x` for which some witness
makes the expression true. -/
theorem mem_language_toCircuit (x : Fin n → Bool) :
    x ∈ (toCircuit n w e he).Language ↔ ∃ wit : Fin w → Bool, e.eval (Fin.append x wit) = true := by
  have key : ∀ wit : Fin w → Bool,
      (toCircuit n w e he).evalAux x wit (toCircuit n w e he).outW = e.eval (Fin.append x wit) := by
    intro wit
    rw [evalAux_toCircuit e he x wit, toCircuit_outW, evalWire_compile]
  exact exists_congr fun wit => by rw [key wit]

end BExpr

end LatticePrepro
