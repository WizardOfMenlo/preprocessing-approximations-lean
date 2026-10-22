import LatticePrepro.Main
import LatticePrepro.Verifier.ThreeSAT

/-!
# Theorem 5.1 for 3SAT

The main theorems of `Main.lean` are stated for an arbitrary quadratic verifier. Instantiating
them with the verifier circuit of `Verifier/ThreeSAT.lean` (Claim 3.11 and Definition 3.10 turn
it into a quadratic verifier with the same language) gives the paper's Theorem 5.1 for 3SAT:
fixed codes and lattices of dimension `M ≤ n^C`, where `n = (2v)^3` is the instance length of
3SAT on `v` variables, with targets `t_x` such that satisfiable instances have
`dist(t_x, ·) ≤ R` and unsatisfiable ones `dist(t_x, ·) > M^{1/s - ε} · R`.
-/

namespace LatticePrepro

namespace ThreeSAT

/-- The quadratic verifier of the 3SAT verifier circuit over `𝔽_p`. -/
abbrev verifier (p v : ℕ) : QuadraticVerifier p := (circuit v).toGateVerifier.toQuadratic p

/-- The quadratic verifier accepts exactly the (encodings of) satisfiable instances. -/
theorem mem_language_verifier_iff (p : ℕ) [Fact p.Prime] {v : ℕ} (x : Instance v) :
    encode x ∈ (verifier p v).Language ↔ Satisfiable x := by
  show encode x ∈ ((circuit v).toGateVerifier.toQuadratic p).Language ↔ _
  rw [GateVerifier.language_toQuadratic, BoolCircuit.language_toGateVerifier, mem_language_iff]

/-- The size parameter `S + 1` of the quadratic verifier is at most `n^3`, `n = len v`. -/
theorem S_verifier_succ_le (p : ℕ) {v : ℕ} (hv : 1 ≤ v) :
    (verifier p v).S + 1 ≤ len v ^ 3 :=
  S_succ_le_len_pow hv

/-- The language of satisfiable 3SAT instances on `v` variables. -/
def SAT (v : ℕ) : Set (Instance v) := {x | Satisfiable x}

/-- **Theorem 5.1 for 3SAT, codes**: for every finite field `F` of characteristic `p` and every
`0 < ε < 1`, there is a constant `C` such that for every `v ≥ 1` there is a fixed code of block
length `M ≤ n^C` (`n = (2v)^3` the instance length) with gap `M^{1 - ε}` for 3SAT on `v`
variables. -/
theorem exists_code_gap (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (CodeGap F ε (SAT v) (len v) C) := by
  refine ⟨3 * sizeExp p (1 - ε), fun v hv => ?_⟩
  obtain ⟨G⟩ := code_gap p F ε hε hε1 (verifier p v)
  refine ⟨G.comap encode (fun x => mem_language_verifier_iff p x) ?_⟩
  rw [pow_mul]
  exact Nat.pow_le_pow_left (S_verifier_succ_le p hv) _

/-- **Theorem 5.1 for 3SAT, lattices**: for every norm exponent `1 ≤ p ≤ ∞` with
`s = min {p, 2}` and every `0 < ε < 1/s`, there is a constant `C` such that for every `v ≥ 1`
there is a fixed full-rank lattice `Λ ⊆ ℤ^M` with `M ≤ n^C` (`n = (2v)^3` the instance length)
and gap `M^{1/s - ε}` for 3SAT on `v` variables. -/
theorem exists_lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → Nonempty (LatticeGap pn ε (SAT v) (len v) C) := by
  refine ⟨3 * sizeExp 2 (1 - pn.s * ε), fun v hv => ?_⟩
  obtain ⟨G⟩ := lattice_gap pn ε hε hε1 (verifier 2 v)
  refine ⟨G.comap encode (fun x => mem_language_verifier_iff 2 x) ?_⟩
  rw [pow_mul]
  exact Nat.pow_le_pow_left (S_verifier_succ_le 2 hv) _

end ThreeSAT

end LatticePrepro
