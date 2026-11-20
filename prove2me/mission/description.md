## Decoding fixed codes and lattices

In the **nearest codeword problem** (NCP) one is given a linear code $\mathcal C \subseteq \mathbb F^M$ over a finite field and a target word $t \in \mathbb F^M$, and must find a codeword closest to $t$ in Hamming distance. In the **closest vector problem** (CVP) one is given a full-rank lattice $\Lambda \subseteq \mathbb R^M$ and a target $t \in \mathbb R^M$, and must find a lattice point closest to $t$ in an $\ell_p$ norm. Both problems are NP-hard to solve exactly, so the question is the approximation factor $f \ge 1$ that efficient algorithms can reach.

In coding theory and in lattice-based cryptography the code or lattice is usually fixed long in advance, and only the target changes. This motivates the **preprocessing model** [FM04]: an algorithm may first spend unbounded time on the code or lattice alone and store a polynomial-length advice string; afterwards it receives targets and must answer each in polynomial time. With preprocessing, NCP over a fixed field is approximable within $O(M/\log M)$ [APY10], and the gap version of CVP within $O(\sqrt{M/\log M})$ in $\ell_2$ [AR05] and $O(\sqrt M)$ in $\ell_p$ for $p \ge 2$ [Peikert08].

Timeline of hardness results:

- **1997–2003, without preprocessing.** Arora, Babai, Stern and Sweedyk prove NP-hardness of every constant factor [ABSS97]; Dinur, Kindler, Raz and Safra reach $M^{c/\log\log M}$ for CVP [DKRS03].
- **2004–2014, with preprocessing.** Feige and Micciancio introduce the model and prove hardness of small constant factors [FM04]. Khot, Popat and Vishnoi reach $2^{(\log M)^{1-\varepsilon}}$, assuming that NP has no circuits of size $2^{(\log n)^{O(1/\varepsilon)}}$ [KPV14].
- **2026, without preprocessing.** Polynomial factors become NP-hard: $M^{1/200}$ for binary codes and $M^{1/400}$ for $\ell_2$ lattices [OAI26, Ch. 7], improved by Song to $M^{1-\varepsilon}$ and $M^{1/2-\varepsilon}$ [Song26].
- **2026, with preprocessing.** Fenzi and Weissenberg prove the same polynomial factors with preprocessing, under $\mathsf{NP} \not\subseteq \mathsf{P/poly}$ [FW26]. This mission formalizes the combinatorial core of that result, and of the paper's second reduction, from query-oblivious PCPs (Theorem 6.4).

## Setting

Fix a finite field $\mathbb F$. A **fixed code with targets** for instances $x \in X$ consists of a finite coordinate set of size $M$, a linear subspace $\mathcal C \subseteq \mathbb F^M$, and a target $t_x \in \mathbb F^M$ for every instance. The distance $\operatorname{dist}(t, \mathcal C)$ is the least Hamming distance from $t$ to a codeword.

Fix a norm exponent $p \in [1, \infty]$ and set $s = \min\{p, 2\}$ (so $s = 2$ for $p = \infty$). A **fixed lattice with targets** consists of a $\mathbb Z$-submodule $\Lambda \subseteq \mathbb Z^M$ that contains $N \cdot \mathbb Z^M$ for some integer $N \ge 1$ (hence has full rank), and an integer target $t_x \in \mathbb Z^M$ for every instance. The distance $\operatorname{dist}_p(t, \Lambda)$ is the infimum of $\|t - v\|_p$ over $v \in \Lambda$; it is attained.

Instances are 3SAT formulas on $v$ variables, written as bit strings $x \in \{0,1\}^n$ with $n = (2v)^3$: one bit for each of the $(2v)^3$ ordered triples of literals, recording whether that clause is present. $\mathrm{SAT}_v$ is the set of satisfiable instances.

The point of the preprocessing model is visible in the order of quantifiers: the code or lattice depends only on $v$, and only the target depends on the instance $x$.

## Formalization targets

### Goal: fixed code and lattice gaps for 3SAT (Theorem 5.1)

For every finite field $\mathbb F$ and every $0 < \varepsilon < 1$ there is a constant $C$ such that for every $v \ge 1$ there are a fixed code $\mathcal C_v \subseteq \mathbb F^M$ with $1 \le M \le n^C$, targets $t_x$ and an integer radius $R \ge 1$ with

$$x \in \mathrm{SAT}_v \implies \operatorname{dist}(t_x, \mathcal C_v) \le R, \qquad x \notin \mathrm{SAT}_v \implies \operatorname{dist}(t_x, \mathcal C_v) > M^{1-\varepsilon} \cdot R.$$

For every $p \in [1, \infty]$ and every $0 < \varepsilon < 1/s$ there is a constant $C$ such that for every $v \ge 1$ there are a fixed full-rank lattice $\Lambda_v \subseteq \mathbb Z^M$ with $1 \le M \le n^C$, integer targets $t_x$ and an integer radius $R \ge 1$ with

$$x \in \mathrm{SAT}_v \implies \operatorname{dist}_p(t_x, \Lambda_v) \le R, \qquad x \notin \mathrm{SAT}_v \implies \operatorname{dist}_p(t_x, \Lambda_v) > M^{1/s-\varepsilon} \cdot R.$$

In the goal, $\mathcal C_v$, $\Lambda_v$, $t_x$ and $R$ are the objects that the paper constructs, not arbitrary ones. $\mathcal C_v$ is the code $\ker A \times \{0\}$ of the fixed linear system $A v = b_x$ of Construction 4.5 for the 3SAT verifier, extended to $\mathbb F$, and $t_x$ is the target of Lemma 3.11. $\Lambda_v$, its targets and its radius are those of Lemma 3.12 for the same system. The instance enters only through the right-hand side $b_x$.

### Milestones

The milestones follow the paper's proof: the verifier and its quadratic equations (Definitions 3.13–3.14, Claim 3.15, the 3SAT circuit); the fixed-verifier linear system and its gap (Theorem 4.6); the explicit moment representations of Appendix A (Theorems A.7 and A.8); the size and gap bound (Theorem 4.8); the conversion to lattices (Lemma 3.12); the test of search outputs (Lemma 5.2); and Theorem 5.1 for an arbitrary quadratic verifier, from which the 3SAT form follows.

Each step that the paper proves by a construction has a milestone for the object it constructs: Theorem 4.8 for the fixed linear system of Construction 4.5, Lemma 3.12 for the Construction A lattice and its Walsh–Hadamard transform, and Theorem 5.1 for the resulting code and lattice. The milestones marked "existence form" assert only that some object with the stated properties exists.

### Further milestones: the reduction from query-oblivious PCPs (Theorem 6.4)

Section 6 of the paper gives a second reduction, which does not use the moment method and is not needed for the goal. It starts from a PCP that is **query-oblivious** with enumerable predicate families: the query locations $I_r$ and the family $\mathcal D_r$ of possible acceptance predicates depend only on the random string $r$, not on the instance (Definition 6.1). The variables are the accepting views of the verifier, and an injective linear map $\iota \colon \mathbb F^{\mathsf m} \to \mathbb F^B$ encodes, for every proof location $u$ and every symbol $a$, the variables of the views that answer $a$ at $u$ (Construction 6.2).

Let the PCP have alphabet $\Sigma$, $\mathsf R$ random bits, $\mathsf q$ queries, perfect completeness and soundness error $\mathsf s$ for a language $L$, let the code $\iota(\mathbb F^{\mathsf m})$ have relative distance $\delta$, and let $\Gamma < \delta \cdot \mathsf s^{-1/\mathsf q}$ be an integer. Then the resulting fixed code $C$ and targets $y_x$ satisfy, with $Y = B \cdot 2^{\mathsf R} \cdot \mathsf q$,

$$x \in L \implies \operatorname{dist}(y_x, C) \le Y, \qquad x \notin L \implies \operatorname{dist}(y_x, C) > \Gamma \cdot Y,$$

and the block length is $(|\Sigma| + \Gamma) \cdot Y + 1$.

Five milestones cover this theorem: the bound on the number of accepting views, the inequality (31) behind the soundness proof, completeness, soundness, and the full statement.

## Significance

Theorem 5.1 is the combinatorial heart of the paper's main result: unless $\mathsf{NP} \subseteq \mathsf{P/poly}$, no preprocessing algorithm with polynomial advice and polynomial online time approximates NCP within $M^{1-\varepsilon}$ or CVP in $\ell_p$ within $M^{1/s-\varepsilon}$. These are the first polynomial hardness factors in the preprocessing model, and for NCP and the gap version of CVP they nearly match the best preprocessing algorithms. Hardness with preprocessing is the relevant notion for decoding problems in which the code or lattice is a public parameter.

Theorem 6.4 reduces languages with query-oblivious PCPs to NCP with preprocessing without the smoothness assumption of [KPV14]. With known PCPs the paper derives from it hardness within $M^{\Omega(1/(\log\log M)^2)}$, unless $\mathsf{NP}$ has circuits of size $n^{O(\log\log n)}$ (Corollary 6.6), a factor that is weaker than the main bounds but already larger than that of [KPV14].

The result is proved in an unrefereed manuscript (a STOC 2027 submission). Its proof combines a moment-based encoding of verifier computations, explicit evaluation tables over finite-field towers, a Hankel-matrix reconstruction argument and code-to-lattice conversions; each of these steps is checked here. A complete Lean 4 / Mathlib proof of every statement in this mission exists and is uploaded with it; the mission's role is to make that development auditable statement by statement.

## Difficulty

The polynomial-factor reductions of [OAI26, Song26] produce a linear system $A_x \cdot w = b$ from each formula $x$; the code is $\ker A_x$ and the target any solution. In the preprocessing model the matrix must depend on the input length alone, with $x$ entering only the right-hand side. Replacing the clause system by a fixed verifier circuit almost achieves this, but the instance still appears in the input equations as a coefficient, $x_i$ times a moment of an unknown table. The term cannot simply be moved to the right-hand side, because in an honest solution that moment depends on the witness, not on $x$ alone. Soundness has to be re-established for a system in which the formula is visible only through the target.

A second difficulty is quantitative: the gap must be $M^{1/s-\varepsilon}$ in terms of the final block length or dimension $M$, which is much larger than $n$, so the size of every component of the construction must be controlled with explicit exponents.

## Formalization scope

- **Codes** are subspaces `Submodule F (M → F)` over an arbitrary finite field `F` that is an algebra over $\mathbb F_p$; distances are natural numbers (`sInf` of the Hamming distances, attained).
- **Lattices** are $\mathbb Z$-submodules of $\mathbb Z^M$ together with an explicit $N \ge 1$ with $N \cdot \mathbb Z^M \subseteq \Lambda$. A milestone identifies them with Mathlib's `IsZLattice` and the distance with `Metric.infDist` in `PiLp`. The exponent $p$ ranges over all real $p \ge 1$ and $p = \infty$ (the paper restricts to rational $p$ for computability).
- **The goal names the construction.** The code is `Tables.codeFamily` and the lattice is `Tables.latticeFamily`, both defined from the fixed linear system of Construction 4.5. What is asserted to exist is the *tables*: a base and an explicit moment representation (Theorem A.8), which do not depend on the instance. The constant $C$ is existential in the goal; the milestones give it explicitly as `sizeExp`.
- **Existence form.** Theorem 5.1 is also stated as `Nonempty` of a structure (`CodeGap`, `LatticeGap`) that bundles some code or lattice with targets, a radius and the bounds. This was the mission's first goal. Since the targets are not required to be computable, this form is also satisfied by a construction unrelated to the paper, in which the target records whether the instance is satisfiable. It is kept as milestones for reference; the statements to rely on are the ones for the paper's construction.
- **Not formalized:** the polynomial-time computability of the maps $1^n \mapsto (\mathcal C, R)$ and $x \mapsto t_x$, the description lengths, the running time of the search test, and therefore the complexity-theoretic consequence (Theorem 1.1, Claim 3.5). Theorem 5.4 and Corollary 5.5 are also out of scope.
- **Theorem 6.4** is formalized for an abstract query-oblivious PCP (`ObliviousPCP`), an arbitrary language and an arbitrary field: completeness, soundness and the block length of the accepting-view code. The copies of each block of the matrix $G_1$ are indexed by the queries $(r, j)$, which gives the paper's matrix up to the order of its rows. The theorem assumes only $\mathsf s > 0$ and a lower bound $\delta$ on the relative distance, and needs neither $\Gamma \ge 2$ nor $\mathsf s < 1$. Its running-time claims are not formalized, and neither are the PCPs of Theorem 6.5, which the paper takes from the literature, or Corollary 6.6.
- **Search test (Lemma 5.2)** is formalized for the paper's concrete tests (a distance threshold for codes, the residual-weight threshold for lattices), as separate milestones. It is not a field of `CodeGap` or `LatticeGap`: without the running-time bound, an abstract "test" field would be satisfied by membership in $\mathrm{SAT}_v$ itself.

## Selected references

- [FW26] G. Fenzi, G. Weissenberg, *Nearly Optimal Hardness for CVP and NCP with Preprocessing*, STOC 2027 submission #847, 2026. IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634. STOC 2027 submissions: https://sigact-stoc.github.io/stoc2027/
- [ABSS97] S. Arora, L. Babai, J. Stern, Z. Sweedyk, *The hardness of approximate optima in lattices, codes, and systems of linear equations*, J. Comput. Syst. Sci. 54:317–331, 1997. https://doi.org/10.1006/jcss.1997.1472
- [DKRS03] I. Dinur, G. Kindler, R. Raz, S. Safra, *Approximating CVP to within almost-polynomial factors is NP-hard*, Combinatorica 23:205–243, 2003. https://doi.org/10.1007/s00493-003-0019-y
- [FM04] U. Feige, D. Micciancio, *The inapproximability of lattice and coding problems with preprocessing*, J. Comput. Syst. Sci. 69:45–67, 2004. https://doi.org/10.1016/j.jcss.2004.01.002
- [AR05] D. Aharonov, O. Regev, *Lattice problems in NP ∩ coNP*, J. ACM 52:749–765, 2005. https://doi.org/10.1145/1089023.1089025
- [Peikert08] C. Peikert, *Limits on the hardness of lattice problems in $\ell_p$ norms*, Comput. Complex. 17:300–351, 2008. https://doi.org/10.1007/s00037-008-0251-3
- [APY10] N. Alon, R. Panigrahy, S. Yekhanin, *Deterministic approximation algorithms for the nearest codeword problem*, Dagstuhl Seminar Proceedings 09421, 2010. https://doi.org/10.4230/DagSemProc.09421.4
- [KPV14] S. Khot, P. Popat, N. K. Vishnoi, *Almost polynomial factor hardness for closest vector problem with preprocessing*, SIAM J. Comput. 43:1184–1205, 2014. https://doi.org/10.1137/130919623
- [OAI26] OpenAI, *Ten Advances in Mathematics and Theoretical Computer Science*, Chapter 7, 2026. https://cdn.openai.com/pdf/ten-proofs-oai.pdf
- [Song26] Z. Song, *Hardness of Euclidean closest vector within $n^{1/2-\epsilon}$ and binary nearest codeword within $n^{1-\epsilon}$*, Preprints.org, 2026. https://doi.org/10.20944/preprints202608.0796.v2
