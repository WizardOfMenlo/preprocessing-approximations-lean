import LatticePrepro.Conversions.Codes

/-!
# Query-oblivious PCPs (Definition 6.1)

A query-oblivious PCP verifier reads `q ≥ 1` locations of a proof `π ∈ Σ^ℓ`, chosen by a random
string `r ∈ {0,1}^ρ` alone, and applies an acceptance predicate `V_{x,r} : Σ^q → {0,1}` that may
depend on the instance `x`. For the reduction of Section 6 the predicates that can occur for a
random string `r` are listed as a family `𝒟_r` of *labeled* predicates, which does not depend on
`x`.

* `ObliviousPCP X` is this data, for instances in an arbitrary type `X` (the paper takes
  `X = {0,1}^n`). The query tuple `I_r` (`query`) and the families `𝒟_r` (`Pred`, `eval`) do not
  take the instance as an argument; the verifier (`verifier`) returns the label of `V_{x,r}`.
* `PerfectlyComplete Lang` and `SoundnessError Lang ε` are perfect completeness and soundness
  error `ε` with respect to a language `Lang ⊆ X`.
* `View r` is the set `𝒱_r` of accepting views for `r`, and `Views` is the set of all accepting
  views; `card_views_le` is the bound `m ≤ 2^ρ · K · |Σ|^q` on their number `m`.

Notation: the symbols follow the paper, except that the number of random bits is `ρ` (the
paper's `𝖱`) and the soundness error is `ε` (the paper's `𝗌`). The bound `K` on the number of
predicates per random string is the paper's `𝗸`.

The running times of the verifier and of the predicate enumerator are not formalized.
-/

namespace LatticePrepro

/-- A query-oblivious PCP verifier with enumerable predicate families (Definition 6.1), for
instances in `X`. -/
structure ObliviousPCP (X : Type) where
  /-- The alphabet `Σ`. -/
  Alphabet : Type
  [fintypeAlphabet : Fintype Alphabet]
  [decEqAlphabet : DecidableEq Alphabet]
  /-- The proof length `ℓ`. -/
  ℓ : ℕ
  /-- The number `ρ` of random bits. -/
  ρ : ℕ
  /-- The number `q` of queries. -/
  q : ℕ
  /-- The verifier makes at least one query. -/
  q_pos : 0 < q
  /-- The query tuple `I_r = (u_{r,1}, …, u_{r,q})`. It does not depend on the instance. -/
  query : (Fin ρ → Bool) → Fin q → Fin ℓ
  /-- The labels of the predicate family `𝒟_r`. It does not depend on the instance. -/
  Pred : (Fin ρ → Bool) → Type
  [fintypePred : ∀ r, Fintype (Pred r)]
  [decEqPred : ∀ r, DecidableEq (Pred r)]
  /-- The predicate `Σ^q → {0,1}` with a given label. Different labels may give the same
  function. -/
  eval : (r : Fin ρ → Bool) → Pred r → (Fin q → Alphabet) → Bool
  /-- The label in `𝒟_r` of the acceptance predicate `V_{x,r}`. -/
  verifier : X → (r : Fin ρ → Bool) → Pred r

namespace ObliviousPCP

attribute [instance] fintypeAlphabet decEqAlphabet fintypePred decEqPred

variable {X : Type} (P : ObliviousPCP X)

/-- Random strings `r ∈ {0,1}^ρ`. -/
abbrev Rand : Type := Fin P.ρ → Bool

/-- Proofs `π ∈ Σ^ℓ`. -/
abbrev Proof : Type := Fin P.ℓ → P.Alphabet

/-- The verifier accepts the proof `π` on instance `x` and random string `r`:
`V_{x,r}(π|_{I_r}) = 1`. -/
def Accepts (x : X) (r : P.Rand) (π : P.Proof) : Prop :=
  P.eval r (P.verifier x r) (fun j => π (P.query r j)) = true

instance (x : X) (r : P.Rand) (π : P.Proof) : Decidable (P.Accepts x r π) :=
  inferInstanceAs (Decidable (P.eval r (P.verifier x r) (fun j => π (P.query r j)) = true))

/-- Perfect completeness: every instance in `Lang` has a proof that is accepted for every random
string. -/
def PerfectlyComplete (Lang : Set X) : Prop :=
  ∀ x ∈ Lang, ∃ π : P.Proof, ∀ r, P.Accepts x r π

/-- Soundness error `ε`: for an instance outside `Lang`, every proof is accepted for at most an
`ε` fraction of the `2^ρ` random strings. -/
def SoundnessError (Lang : Set X) (ε : ℝ) : Prop :=
  ∀ x, x ∉ Lang → ∀ π : P.Proof,
    ((Finset.univ.filter fun r => P.Accepts x r π).card : ℝ) ≤ ε * 2 ^ P.ρ

/-- The accepting views `𝒱_r` for the random string `r`: pairs `(V, a)` of a labeled predicate
`V ∈ 𝒟_r` and an answer tuple `a ∈ Σ^q` with `V(a) = 1` and `a = π|_{I_r}` for some proof `π`,
that is, `a_j = a_{j'}` whenever `u_{r,j} = u_{r,j'}`. -/
abbrev View (r : P.Rand) : Type :=
  {p : P.Pred r × (Fin P.q → P.Alphabet) //
    P.eval r p.1 p.2 = true ∧ ∀ j j', P.query r j = P.query r j' → p.2 j = p.2 j'}

variable {P} in
/-- The labeled predicate of an accepting view. -/
def View.pred {r : P.Rand} (w : P.View r) : P.Pred r := w.1.1

variable {P} in
/-- The answer tuple of an accepting view. -/
def View.ans {r : P.Rand} (w : P.View r) : Fin P.q → P.Alphabet := w.1.2

variable {P} in
lemma View.eval_eq {r : P.Rand} (w : P.View r) : P.eval r w.pred w.ans = true := w.2.1

variable {P} in
lemma View.ans_eq {r : P.Rand} (w : P.View r) {j j' : Fin P.q}
    (h : P.query r j = P.query r j') : w.ans j = w.ans j' := w.2.2 j j' h

/-- All accepting views, over all random strings. Their number is `m`. -/
abbrev Views : Type := Σ r : P.Rand, P.View r

/-- The number of random strings is `2^ρ`. -/
lemma card_rand : Fintype.card P.Rand = 2 ^ P.ρ := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- The number of accepting views is at most `2^ρ · K · |Σ|^q`, where `K` bounds the number of
predicates per random string (proof of Theorem 6.4, size). -/
theorem card_views_le {K : ℕ} (hK : ∀ r, Fintype.card (P.Pred r) ≤ K) :
    Fintype.card P.Views ≤ 2 ^ P.ρ * K * Fintype.card P.Alphabet ^ P.q := by
  have h : ∀ r : P.Rand, Fintype.card (P.View r) ≤ K * Fintype.card P.Alphabet ^ P.q := by
    intro r
    calc Fintype.card (P.View r) ≤ Fintype.card (P.Pred r × (Fin P.q → P.Alphabet)) :=
          Fintype.card_subtype_le _
      _ = Fintype.card (P.Pred r) * Fintype.card P.Alphabet ^ P.q := by
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      _ ≤ K * Fintype.card P.Alphabet ^ P.q := Nat.mul_le_mul_right _ (hK r)
  calc Fintype.card P.Views = ∑ r : P.Rand, Fintype.card (P.View r) := Fintype.card_sigma
    _ ≤ ∑ _r : P.Rand, K * Fintype.card P.Alphabet ^ P.q := Finset.sum_le_sum fun r _ => h r
    _ = 2 ^ P.ρ * K * Fintype.card P.Alphabet ^ P.q := by
        rw [Finset.sum_const, Finset.card_univ, P.card_rand, smul_eq_mul, mul_assoc]

end ObliviousPCP

end LatticePrepro
