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

The polynomial-time computability claims of the paper (and hence the complexity-theoretic wrapper
`NP ⊄ P/poly ⇒ no preprocessing algorithm`, Claim 3.5, and the running-time part of Lemma 5.2) are
**not** formalized. Everything else on the path to Theorem 5.1 is, including the explicit
evaluation tables of Appendix A, the code/lattice conversions of Appendix B, the search test of
Lemma 5.2, and a verifier circuit family for 3SAT. Section 6 (the PCP-based reduction), the ETH
endpoint theorem (Theorem 5.3) and Corollary 5.4 are out of scope.

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
| `exists_explicit_momentRepresentation` (`Tables/Explicit.lean`) | Thm. A.7 | an `ExplicitMomentRepresentation`: `r = B^m`, `D = q` blocks of size `q^m`, `q` a power of `p`, `B ≤ q < 8 p^3 m S B` |
| `exists_gapReduction` (`Main.lean`) | Thm. 4.7 | a `GapReduction`: gap `g < b`, `b` a power of `p`, `n^m ≤ (8 p^4 m (S+1))^{(m+7) m} g^{m+1}` columns |
| `exists_latticeReduction` (`Conversions/Lattices.lean`) | Lem. 3.8 | a `LatticeReduction`: fixed full-rank lattice in `ℤ^M`, `2n ≤ M < 4n`, radius `1 ≤ R ≤ M`, residual weight `w ≤ 16 D (dist/R)^s`, `w > g D` on NO instances |
| `CodeFamily.accepts_of_isApprox`, `CodeFamily.not_accepts_of_lt`, `LatticeReduction.accepts_of_isApprox`, `LatticeReduction.not_accepts_of_isNo` (`Conversions/SearchTest.lean`) | Lem. 5.2 | the test "residual weight `≤ g D`" accepts every `f`-approximate solution on YES instances (`16 f^s ≤ g`) and rejects every vector on NO instances |
| `code_gap`, `exists_code_gap` (`Main.lean`) | Thm. 5.1 (codes) | a `CodeGap`: fixed code over any finite field of characteristic `p`, `M ≤ (S+1)^C`, `dist(t_x, 𝒞) ≤ R` on YES and `> M^{1-ε} R` on NO instances, with the search test; `C = sizeExp p (1-ε)` is explicit |
| `lattice_gap`, `exists_lattice_gap` (`Main.lean`) | Thm. 5.1 (lattices) | a `LatticeGap`: fixed full-rank lattice in `ℤ^M`, any `ℓ_p` (`PNorm`), `M ≤ (S+1)^C`, `dist_p(t_x, Λ) ≤ R` on YES and `> M^{1/s-ε} R` on NO instances, with the search test; `C = sizeExp 2 (1 - s ε)` is explicit |
| `ThreeSAT.mem_language_iff` (`Verifier/ThreeSAT.lean`) | Thm. 5.1 ("a verifier for 3SAT") | the Boolean circuit `ThreeSAT.circuit v` with `n = (2v)^3` inputs and `S ≤ 9n + 2` wires accepts exactly the satisfiable 3SAT instances on `v` variables |
| `ThreeSAT.exists_code_gap`, `ThreeSAT.exists_lattice_gap` (`ThreeSAT.lean`) | Thm. 5.1 | the two previous rows for 3SAT: `M ≤ n^C` in the instance length `n` |
| `LatticeFamily.latticeDist_eq_infDist`, `LatticeFamily.isZLattice_realLattice` (`Lattices/Mathlib.lean`) | Def. 2.1 | `dist_p(t, Λ)` is Mathlib's `Metric.infDist` in `PiLp`, and the lattices are `IsZLattice`s |
| `GateVerifier.language_toQuadratic`, `BoolCircuit.language_toGateVerifier` | Claim 3.11, Def. 3.9–3.10 | Boolean circuits with fan-in-two gates define the same language as their quadratic verifier |

All results except the 3SAT ones are stated for an arbitrary `QuadraticVerifier` (a system of
quadratic equations over `𝔽_p` with a designated input prefix and output coordinate). The
constant `C` in Theorem 5.1 depends only on `p` (resp. the field) and `ε`, and is given by the
explicit function `sizeExp`.

## Structure

| File | Paper | Content |
| --- | --- | --- |
| `Basic/Blocks.lean` | §3 | binary / block-sparse vectors, Hamming weight by blocks |
| `Basic/Matrix.lean`, `Basic/Hamming.lean`, `Basic/Finset.lean`, `Basic/RealSums.lean`, `Basic/FiniteField.lean`, `Basic/Nat.lean` | — | generic lemmas (minors and ranks of polynomial matrices, Hamming weights on sum types, telescoping sums, power-mean inequalities, Frobenius fixed points, geometric sums and powers in ranges) |
| `Moments/Basic.lean` | Def. 4.1–4.2, Lem. 4.3, (4.4) | coefficient functions as `Ω →₀ 𝔽_p`, moments, Vandermonde identification, translation moments |
| `Moments/Representation.lean` | Def. 4.4 | abstract `MomentRepresentation` (completeness/soundness of evaluation tables), moment orders `Fin (2r - 1)` |
| `Verifier/Quadratic.lean` | Def. 3.9–3.10 | `QuadraticVerifier`, prefixes, language, encoding tuples `E`, instance encoding `θ_x` |
| `Verifier/Gates.lean`, `Verifier/Circuit.lean` | Claim 3.11 | gate verifiers and acyclic Boolean circuits, reduced to quadratic verifiers |
| `Verifier/Expr.lean`, `Verifier/ThreeSAT.lean` | Thm. 5.1 | Boolean expressions compiled to circuits; the 3SAT verifier circuit family |
| `Reduction/LinearSystem.lean` | Def. 3.6 | `LinearSystemFamily` (fixed matrix `A`, instance-dependent `rhs`), BSLSP promises |
| `Reduction/FixedSystem.lean` | Constr. 4.5 | the fixed-verifier system (tables, representatives, the equation left-hand sides, the linear map) |
| `Reduction/Completeness.lean`, `Reduction/Soundness.lean` | Thm. 4.6, Lem. 4.8 | honest solution and telescoping; recovery of assignments and the coset sum |
| `Tables/Digits.lean` | Def. A.1, Claim A.2 | generalized digits |
| `Tables/FieldSetup.lean` | Lem. A.3 (existence) | sample field `𝕊`, extension `K = 𝕊(γ)` of prescribed degree |
| `Tables/PolyMatrixRank.lean` | Lem. A.5 | rank of a polynomial matrix vs. its evaluations (Fancsali–Sziklai) |
| `Tables/Hankel.lean` | Thm. A.6 | moment reconstruction from a Hankel matrix with Frobenius constraints |
| `Tables/Construction.lean`, `Tables/ElementTable.lean`, `Tables/TableSoundness.lean`, `Tables/Explicit.lean` | Constr. A.4, Thm. A.7 | polynomial evaluation tables, element tables, soundness, assembly into an `ExplicitMomentRepresentation` |
| `Conversions/Codes.lean` | Lem. 3.7, App. B.1 | fixed codes from linear systems; extension of scalars |
| `Conversions/LpNorm.lean`, `Conversions/ConstructionA.lean`, `Conversions/Hadamard.lean`, `Conversions/Padding.lean`, `Conversions/Lattices.lean` | Lem. 3.8, App. B.2–B.3 | `ℓ_p` norms, Construction A, Walsh–Hadamard blocks, padding, the lattice reduction (`LatticeReduction`) |
| `Conversions/SearchTest.lean` | Lem. 5.2 | testing search outputs for codes and lattices |
| `Lattices/Basis.lean` | (B.2) | a sublattice containing `N · ℤ^M` has a `ℤ`-basis indexed by `Fin M` |
| `Lattices/Distance.lean`, `Lattices/Mathlib.lean` | Def. 2.1 | `dist_p(t, Λ)` as an attained infimum; identification with `PiLp` norms, `Metric.infDist` and `IsZLattice` |
| `Main.lean` | Thm. 4.7, Thm. 5.1 | choice of `B`, `m`, `g = (S+1)^k` (explicit `momentAxes`, `gapExp`, `sizeExp`); the final theorems |
| `ThreeSAT.lean` | Thm. 5.1 | the final theorems instantiated with the 3SAT verifier |

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
  fan-in-two gates reduce to them (Claim 3.11). The 3SAT verifier is a Boolean circuit built by
  compiling a Boolean expression (`Verifier/Expr.lean`). 3SAT instances on `v` variables are
  encoded, as in the paper's proof of Theorem 5.3, by one bit for each of the `(2v)^3` possible
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
* Two lemmas acquired the (necessary) hypothesis that the number of blocks is positive
  (`LinearSystemFamily.code_no`, `exists_latticeReduction`); it holds for every fixed-verifier
  system.
