# Lean formalization: nearly optimal hardness for CVP and NCP with preprocessing

[![CI](https://github.com/WizardOfMenlo/preprocessing-approximations-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/WizardOfMenlo/preprocessing-approximations-lean/actions/workflows/ci.yml)

This repository contains a Lean 4 / Mathlib formalization of the mathematical content of the
main result of *Nearly Optimal Hardness for CVP and NCP with Preprocessing* (Fenzi, Weissenberg):
for every verifier, there is a **fixed** code (over any finite field) or a **fixed** lattice (in any
`ℓ_p` norm, `1 ≤ p ≤ ∞`) of polynomial dimension `M`, together with a target for every instance,
such that YES instances have distance at most `R` and NO instances have distance more than
`M^{1/s - ε} · R` (`s = 1` for codes, `s = min {p, 2}` for lattices). The verifier is
instantiated with a concrete circuit family for 3SAT, which gives the paper's Theorem 5.1 with
`M ≤ n^C` in the instance length `n`.

The theorem is stated in two forms. The existence form (`CodeGap`, `LatticeGap`) says that some
fixed code or lattice with targets has the gap. On its own it says very little: the paper also
requires the map `x ↦ t_x` to be polynomial-time computable, and without that requirement a
two-coordinate code whose target records whether `x` is in the language already satisfies it.
The form to rely on is the one in `Explicit.lean`, which proves the gap for the code and the
lattice that the paper constructs: the instance enters only through the right-hand side of the
fixed linear system of Construction 4.5, and only instance-independent tables are asserted to
exist.

The polynomial-time computability claims of the paper (and hence the complexity-theoretic wrapper
`NP ⊄ P/poly ⇒ no preprocessing algorithm`, Claim 3.5, and the running-time part of Lemma 5.2) are
**not** formalized. Everything else on the path to Theorem 5.1 is, including the explicit
evaluation tables of Appendix A, the code/lattice conversions of Appendix B, the search test of
Lemma 5.2 (for the paper's concrete tests, as separate lemmas: without the running-time bound, a
test bundled abstractly into `CodeGap`/`LatticeGap` could be the language's membership predicate),
and a verifier circuit family for 3SAT.

The reduction from query-oblivious PCPs of Section 6 (Theorem 6.4) is formalized as well, for an
abstract PCP: completeness, soundness and the block length of the accepting-view code. The PCPs
of Theorem 6.5 are taken from the literature and are not formalized, so Corollary 6.6 is out of
scope, as are the ETH endpoint theorem (Theorem 5.4) and Corollary 5.5.

## Building and checking

With [elan](https://github.com/leanprover/elan) installed (it picks up the toolchain from
`lean-toolchain`), run from the repository root:

```
lake exe cache get   # fetches the Mathlib build cache
lake build
```

Toolchain: `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0`. The library contains no `sorry`;
`#print axioms` on every main theorem reports only `propext`, `Classical.choice`, `Quot.sound`.
Both claims are machine-checked: `lake build` also builds `AxiomCheck.lean`, which pins the axioms
of every theorem listed below with `#guard_msgs` and fails if they change, and CI builds with
`--wfail`, so any warning (in particular `declaration uses 'sorry'`) fails the build.

## Main statements

The outputs of the existence theorems are bundled structures (`GapReduction`, `LatticeReduction`,
`ExplicitMomentRepresentation`, `CodeGap`, `LatticeGap`) whose fields carry the properties; the
theorems assert `Nonempty` of them.

| Lean name | Paper | Statement |
| --- | --- | --- |
| `FixedSystem.isGapReduction` (`Reduction/Soundness.lean`) | Thm. 4.6 | for any moment representation and encoding tuple, the fixed-verifier system is a gap reduction with gap `g` when `2 g N < r` |
| `exists_explicit_momentRepresentation` (`Tables/Explicit.lean`) | Thm. A.8 | an `ExplicitMomentRepresentation`: `r = B^m`, `D = q` blocks of size `q^m`, `q` a power of `p`, `B ≤ q < 8 p^3 m S B` |
| `exists_gapReduction` (`Main.lean`) | Thm. 4.8 | a `GapReduction`: gap `g < b`, `b` a power of `p`, `n^m ≤ (8 p^4 m (S+1))^{(m+7) m} g^{m+1}` columns |
| `exists_latticeReduction` (`Conversions/Lattices.lean`) | Lem. 3.12 | a `LatticeReduction`: fixed full-rank lattice in `ℤ^M`, `2n ≤ M < 4n`, radius `1 ≤ R ≤ M`, residual weight `w ≤ 16 D (dist/R)^s`, `w > g D` on NO instances |
| `CodeFamily.accepts_of_isApprox`, `CodeFamily.not_accepts_of_lt`, `LatticeReduction.accepts_of_isApprox`, `LatticeReduction.not_accepts_of_isNo` (`Conversions/SearchTest.lean`) | Lem. 5.2 | the test "residual weight `≤ g D`" accepts every `f`-approximate solution on YES instances (`16 f^s ≤ g`) and rejects every vector on NO instances |
| `code_gap`, `exists_code_gap` (`Main.lean`) | Thm. 5.1 (codes) | a `CodeGap`: fixed code over any finite field of characteristic `p`, `M ≤ (S+1)^C`, `dist(t_x, 𝒞) ≤ R` on YES and `> M^{1-ε} R` on NO instances; `C = sizeExp p (1-ε)` is explicit |
| `lattice_gap`, `exists_lattice_gap` (`Main.lean`) | Thm. 5.1 (lattices) | a `LatticeGap`: fixed full-rank lattice in `ℤ^M`, any `ℓ_p` (`PNorm`), `M ≤ (S+1)^C`, `dist_p(t_x, Λ) ≤ R` on YES and `> M^{1/s-ε} R` on NO instances; `C = sizeExp 2 (1 - s ε)` is explicit |
| `ThreeSAT.mem_language_iff` (`Verifier/ThreeSAT.lean`) | Thm. 5.1 ("a verifier for 3SAT") | the Boolean circuit `ThreeSAT.circuit v` with `n = (2v)^3` inputs and `S ≤ 9n + 2` wires accepts exactly the satisfiable 3SAT instances on `v` variables |
| `ThreeSAT.exists_code_gap`, `ThreeSAT.exists_lattice_gap` (`ThreeSAT.lean`) | Thm. 5.1 | the two previous rows for 3SAT: `M ≤ n^C` in the instance length `n` |
| `ThreeSAT.fixed_code_and_lattice_gaps` (`ThreeSAT.lean`) | Thm. 5.1 | the previous row as one statement (codes and lattices), in existence form |
| `QuadraticVerifier.Tables.system_spec`, `QuadraticVerifier.Tables.nonempty` (`Explicit.lean`) | Thm. 4.8, Thm. A.8 | for tables `T` (a base `B` and an explicit moment representation), the fixed system `T.system` of Construction 4.5 is a gap reduction with the size bound of Theorem 4.8; tables exist when `S ≥ 2` |
| `LinearSystemFamily.exists_latticeReduction_eq` (`Explicit.lean`) | Lem. 3.12 | the lattice reduction is realized by the explicit `latticeFamily` (Construction A, Hadamard-transformed for `p > 2`) with the explicit radius `latticeRadius` |
| `QuadraticVerifier.Tables.codeFamily_hasGap`, `QuadraticVerifier.Tables.latticeFamily_hasGap` (`Explicit.lean`) | Thm. 5.1 | for every choice of tables, the code `ker A × {0}` of the fixed system (extended to `F`) with the targets of Lemma 3.11, and the lattice of Lemma 3.12, have `M ≤ (S+1)^C` and the gap `M^{1/s-ε}` |
| `ThreeSAT.explicit_code_and_lattice_gaps` (`Explicit.lean`) | Thm. 5.1 | the previous row for the 3SAT verifier, codes and lattices in one statement: Theorem 5.1 for the paper's construction; the goal of the Prove2Me mission (`prove2me/`) |
| `LatticeFamily.latticeDist_eq_infDist`, `LatticeFamily.isZLattice_realLattice` (`Lattices/Mathlib.lean`) | Def. 3.1 | `dist_p(t, Λ)` is Mathlib's `Metric.infDist` in `PiLp`, and the lattices are `IsZLattice`s |
| `GateVerifier.language_toQuadratic`, `BoolCircuit.language_toGateVerifier` | Claim 3.15, Def. 3.13–3.14 | Boolean circuits with fan-in-two gates define the same language as their quadratic verifier |
| `ObliviousPCP.pcp_reduction` (`PCP/Reduction.lean`) | Thm. 6.4 | for a query-oblivious PCP with perfect completeness and soundness error `ε`, an injective encoding `E : F^m → F^B` of relative distance `≥ δ` and `g < δ ε^{-1/q}`: the accepting-view code has `dist(y_x, 𝒞) ≤ Y` on YES and `> g Y` on NO instances, with `Y = B 2^ρ q` and block length `(|Σ| + g) Y + 1` |
| `ObliviousPCP.card_views_le` (`PCP/Verifier.lean`) | Thm. 6.4 (size) | the number of accepting views is at most `2^ρ K |Σ|^q` for `K` predicates per random string |

All results of Sections 3–5 except the 3SAT ones are stated for an arbitrary `QuadraticVerifier`
(a system of quadratic equations over `𝔽_p` with a designated input prefix and output
coordinate), and Theorem 6.4 for an arbitrary `ObliviousPCP` and language. The
constant `C` in Theorem 5.1 depends only on `p` (resp. the field) and `ε`, and is given by the
explicit function `sizeExp`.

## Structure

| File | Paper | Content |
| --- | --- | --- |
| `Basic/Blocks.lean` | §3 | binary / block-sparse vectors, Hamming weight by blocks |
| `Basic/Matrix.lean`, `Basic/Hamming.lean`, `Basic/Finset.lean`, `Basic/RealSums.lean`, `Basic/FiniteField.lean`, `Basic/Nat.lean` | — | generic lemmas (minors and ranks of polynomial matrices, Hamming weights on sum types, telescoping sums, power-mean inequalities, Frobenius fixed points, geometric sums and powers in ranges) |
| `Moments/Basic.lean` | Def. 4.1–4.2, Lem. 4.3, (20) | coefficient functions as `Ω →₀ 𝔽_p`, moments, Vandermonde identification, translation moments |
| `Moments/Representation.lean` | Def. 4.4 | abstract `MomentRepresentation` (completeness/soundness of evaluation tables), moment orders `Fin (2r - 1)` |
| `Verifier/Quadratic.lean` | Def. 3.13–3.14 | `QuadraticVerifier`, prefixes, language, encoding tuples `E`, instance encoding `θ_x` |
| `Verifier/Gates.lean`, `Verifier/Circuit.lean` | Claim 3.15 | gate verifiers and acyclic Boolean circuits, reduced to quadratic verifiers |
| `Verifier/Expr.lean`, `Verifier/ThreeSAT.lean` | Thm. 5.1 | Boolean expressions compiled to circuits; the 3SAT verifier circuit family |
| `Reduction/LinearSystem.lean` | Def. 3.10 | `LinearSystemFamily` (fixed matrix `A`, instance-dependent `rhs`), BSLSP promises |
| `Reduction/FixedSystem.lean` | Constr. 4.5 | the fixed-verifier system (tables, representatives, the equation left-hand sides, the linear map) |
| `Reduction/Completeness.lean`, `Reduction/Soundness.lean` | Thm. 4.6, Lem. 4.7 | honest solution and telescoping; recovery of assignments and the coset sum |
| `Tables/Digits.lean` | Def. A.1, Claim A.2 | generalized digits |
| `Tables/FieldSetup.lean` | Lem. A.3 (existence) | sample field `𝕊`, extension `K = 𝕊(γ)` of prescribed degree |
| `Tables/PolyMatrixRank.lean` | Lem. A.6 | rank of a polynomial matrix vs. its evaluations (Fancsali–Sziklai) |
| `Tables/Hankel.lean` | Thm. A.7 | moment reconstruction from a Hankel matrix with Frobenius constraints |
| `Tables/Construction.lean`, `Tables/ElementTable.lean`, `Tables/TableSoundness.lean`, `Tables/Explicit.lean` | Constr. A.4, Thm. A.8 | polynomial evaluation tables, element tables, soundness, assembly into an `ExplicitMomentRepresentation` |
| `Conversions/Codes.lean` | Lem. 3.11, App. B.1 | fixed codes from linear systems; extension of scalars |
| `Conversions/LpNorm.lean`, `Conversions/ConstructionA.lean`, `Conversions/Hadamard.lean`, `Conversions/Padding.lean`, `Conversions/Lattices.lean` | Lem. 3.12, App. B.2–B.3 | `ℓ_p` norms, Construction A, Walsh–Hadamard blocks, padding, the lattice reduction (`LatticeReduction`) |
| `Conversions/SearchTest.lean` | Lem. 5.2 | testing search outputs for codes and lattices |
| `Lattices/Basis.lean` | (40) | a sublattice containing `N · ℤ^M` has a `ℤ`-basis indexed by `Fin M` |
| `Lattices/Distance.lean`, `Lattices/Mathlib.lean` | Def. 3.1 | `dist_p(t, Λ)` as an attained infimum; identification with `PiLp` norms, `Metric.infDist` and `IsZLattice` |
| `Main.lean` | Thm. 4.8, Thm. 5.1 | choice of `B`, `m`, `g = (S+1)^k` (explicit `momentAxes`, `gapExp`, `sizeExp`); the final theorems |
| `ThreeSAT.lean` | Thm. 5.1 | the final theorems instantiated with the 3SAT verifier |
| `Explicit.lean` | Thm. 5.1 | the final theorems for the paper's construction: `Tables`, the explicit code and lattice families, `HasGap` |
| `PCP/Verifier.lean` | Def. 6.1 | `ObliviousPCP` (query tuples and labeled predicate families independent of the instance), perfect completeness, soundness error, accepting views |
| `PCP/Code.lean` | Constr. 6.2 | the constraint system `G₀ v = b_x`, restrictions `v^{u,a}`, the matrix `G₁`, the accepting-view code and its targets |
| `PCP/Inequality.lean` | (31) | the two Jensen steps as one inequality on positive reals |
| `PCP/Reduction.lean` | Thm. 6.4 | completeness, soundness and block length of the accepting-view code |

## Design notes

* Coefficient functions live on a single extension field `Ω` of the moment field `K` (an
  algebraic closure in the explicit construction), as finitely supported functions `Ω →₀ 𝔽_p`.
  This avoids embedding several finite extensions into a common one.
* Theorem 4.6 is proved for an *abstract* moment representation; the explicit construction of
  Appendix A is a separate module that produces one. The two can be reused independently. Moment
  maps are indexed by the orders `Fin (2r - 1)`, i.e. `0 ≤ k ≤ 2r - 2`, so there are no junk
  orders.
* The equations of Construction 4.5 are given once, as left-hand sides (`encLhs`, `gateLhs`,
  `transLhs`); both the predicate `Solves` and the linear map `sysMap` are defined from them.
* Verifiers are abstracted as systems of quadratic equations over `𝔽_p`; Boolean circuits with
  fan-in-two gates reduce to them (Claim 3.15). The 3SAT verifier is a Boolean circuit built by
  compiling a Boolean expression (`Verifier/Expr.lean`). 3SAT instances on `v` variables are
  encoded, as in the paper's proof of Theorem 5.4, by one bit for each of the `(2v)^3` possible
  clauses.
* As in Construction A.4, the degree of `K/𝕊` is the least power of `p` that is at least `S`,
  and the sample field size `q` is the least power of `p` that is at least `8 p m B δ`. The
  fields are obtained from Mathlib's `GaloisField` (the paper's explicit Artin–Schreier tower
  only matters for the unformalized running-time analysis).
* Size bounds are kept in integer form (`n^m ≤ …`) and converted to real exponents only in the
  final theorems, where the constants `m`, `k`, `C` are the explicit functions `momentAxes`,
  `gapExp`, `sizeExp` of `p` and `δ = 1 - s ε`. The lattice theorems hold for all real `p ≥ 1`
  and `p = ∞` directly (the paper's detour through rational `p` is only needed for
  computability).
* The lattice distance `dist_p(t, Λ)` is an infimum over the lattice, shown to be attained; the
  final theorems are stated with it, and `Lattices/Mathlib.lean` identifies it with
  `Metric.infDist` in `PiLp` and the lattices with Mathlib's `IsZLattice`.
* In Construction 6.2 the `d_u` copies of the block of a location `u` are indexed by the queries
  `(r, j)` with `u_{r,j} = u`, so the coordinates of `G₁` are `(r, j, a, b)`; this is the paper's
  matrix up to the order of its rows. In the soundness proof of Theorem 6.4 the random proof is
  replaced by a count over all proofs with entries in the lists. The theorem needs neither
  `g ≥ 2` nor `ε < 1`, only a lower bound `δ` on the relative distance, and holds over any field.
* `Explicit.lean` exists because an existence statement about codes with arbitrary targets is
  satisfied by a dummy construction once computability is dropped. It names the families:
  `Tables.codeFamily` is `ker A × {0}` for `fixedSystem`, and `Tables.latticeFamily` is the
  lattice of Lemma 3.12. The targets still pick a solution of `A v = b_x` by classical choice
  (the paper uses Gaussian elimination); the distance to the code does not depend on the pick.
  Polynomial-time computability itself remains unformalized.
* Two lemmas acquired the (necessary) hypothesis that the number of blocks is positive
  (`LinearSystemFamily.code_no`, `exists_latticeReduction`); it holds for every fixed-verifier
  system.
