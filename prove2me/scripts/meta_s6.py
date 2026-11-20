#!/usr/bin/env python3
"""Write the metadata of the Section 6 items (Definition 6.1, Construction 6.2, Theorem 6.4):
out/meta/batch_E.json (titles, natural-language statements, sources) and
mission/milestones_s6.json (the milestones added to the live mission).

  python3 meta_s6.py
"""
import json
import os

P = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAPER = ("G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing "
         "(STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), ")
NS = "LatticePrepro.ObliviousPCP."
NAMES = (r"The Lean names `ε`, `E`, `g`, `ρ`, `q` stand for $\mathsf s$, $\iota$, $\Gamma$, "
         r"$\mathsf R$, $\mathsf q$.")
SETUP = (r"Consider Construction 6.2 for a query-oblivious PCP with enumerable predicate families "
         r"(Definition 6.1) with $\mathsf R$ random bits, $\mathsf q\ge1$ queries and $\mathsf m$ "
         r"accepting views, a field $F$, an $F$-linear map $\iota\colon F^{\mathsf m}\to F^{B}$ and "
         r"an integer $\Gamma\ge0$. Let $C$ be its code, $y_x$ its targets, and "
         r"$Y=B\cdot2^{\mathsf R}\cdot\mathsf q$.")
HYPS = (r"""Suppose that

- the PCP has soundness error $\mathsf s>0$ for a language $L$: for every instance $x\notin L$, every proof is accepted for at most $\mathsf s\cdot2^{\mathsf R}$ random strings;
- $\iota$ is injective, and every nonzero vector of the code $\iota(F^{\mathsf m})$ has Hamming weight at least $\delta\cdot B$, for a real number $\delta$;
- $\Gamma<\delta\cdot\mathsf s^{-1/\mathsf q}$, which is condition (28).""")
WEAKER = (r"The hypotheses are weaker than in the paper: $\mathsf s<1$ and $\Gamma\ge2$ are not "
          r"assumed, $\delta$ is only a lower bound on the relative distance of the code "
          r"$\iota(F^{\mathsf m})$, and $F$ need not be finite.")

items = []

items.append({
    "definition_name": "LatticePrepro_PCP_Verifier",
    "definition_title": "Query-oblivious PCPs with enumerable predicate families, and their accepting views (Definition 6.1)",
    "natural_language_statement": r"""These definitions formalize the query-oblivious PCP verifiers used in the reduction of Section 6.

1. **Query-oblivious PCP** (`ObliviousPCP X`). For a set $X$ of instances: a finite alphabet $\Sigma$, a proof length $\ell$, a number $\mathsf R$ of random bits, a number $\mathsf q\ge1$ of queries, and
   - for every random string $r\in\{0,1\}^{\mathsf R}$, a query tuple $I_r=(u_{r,1},\dots,u_{r,\mathsf q})\in[\ell]^{\mathsf q}$;
   - for every $r$, a finite family $\mathcal D_r$ of labeled predicates $\Sigma^{\mathsf q}\to\{0,1\}$, given by a finite set of labels and an evaluation map (different labels may give the same function);
   - for every instance $x\in X$ and every $r$, the label in $\mathcal D_r$ of the acceptance predicate $V_{x,r}$.

   Neither $I_r$ nor $\mathcal D_r$ depends on the instance.
2. **Acceptance** (`Accepts`). The verifier accepts a proof $\pi\in\Sigma^{\ell}$ on the instance $x$ and the random string $r$ if $V_{x,r}(\pi|_{I_r})=1$, where $\pi|_{I_r}=(\pi(u_{r,1}),\dots,\pi(u_{r,\mathsf q}))$.
3. **Perfect completeness** (`PerfectlyComplete`) for a language $L\subseteq X$: every $x\in L$ has a proof that is accepted for every random string.
4. **Soundness error** (`SoundnessError`) $\mathsf s$ for $L$, with $\mathsf s$ a real number: for every $x\notin L$ and every proof $\pi$, the number of random strings for which $\pi$ is accepted is at most $\mathsf s\cdot2^{\mathsf R}$. That is, every proof is accepted with probability at most $\mathsf s$.
5. **Accepting views** (`View`, `Views`). An accepting view for $r$ is a pair $(V,\mathbf a)\in\mathcal D_r\times\Sigma^{\mathsf q}$ with $V(\mathbf a)=1$ and $a_j=a_{j'}$ whenever $u_{r,j}=u_{r,j'}$; the last condition says that $\mathbf a=\pi|_{I_r}$ for some proof $\pi$. The set of accepting views for $r$ is $\mathcal V_r$, and `Views` is the disjoint union of the sets $\mathcal V_r$, of size $\mathsf m=\sum_r|\mathcal V_r|$. `View.pred` and `View.ans` are the two components $V$ and $\mathbf a$ of a view.

This is Definition 6.1 of the paper. The accepting-view code of Construction 6.2 and the reduction of Theorem 6.4 are stated for these objects.

**Formalization Note.** Instances form an arbitrary type $X$ (the paper takes $X=\{0,1\}^{n}$), and $L$ is an arbitrary subset of $X$ rather than the language of a relation. Random strings are functions `Fin ρ → Bool`, proof locations are elements of `Fin ℓ`, and queries are indexed by `Fin q`. The Lean field names `ρ` and `q` stand for $\mathsf R$ and $\mathsf q$, and the theorems call the soundness error `ε`. Predicates take values in `Bool`, and equality of predicates is equality of labels, as in the paper. The running times of the verifier and of the predicate enumerator (the parameter $\mathsf{vt}$) are not formalized.""",
    "source": PAPER + r"Definition 6.1 (\label{def:query-oblivious-pcp}); Lean: LatticePrepro/PCP/Verifier.lean, "
              + ", ".join(NS + n for n in ("Rand", "Proof", "Accepts", "PerfectlyComplete",
                                           "SoundnessError", "View", "View.pred", "View.ans", "Views"))
              .replace(NS + "Rand", "LatticePrepro.ObliviousPCP, " + NS + "Rand"),
})

items.append({
    "definition_name": "LatticePrepro_PCP_Code",
    "definition_title": "The accepting-view code and its targets (Construction 6.2)",
    "natural_language_statement": r"""Fix a query-oblivious PCP as in Definition 6.1 with $\mathsf m$ accepting views, a field $F$, an $F$-linear encoding map $\iota\colon F^{\mathsf m}\to F^{B}$ and an integer $\Gamma\ge0$. These definitions build the fixed code and the targets of Construction 6.2.

1. **Variables.** A vector $v\in F^{\mathsf m}$ has one coordinate $v_{r,V,\mathbf a}$ for every random string $r$ and every accepting view $(V,\mathbf a)\in\mathcal V_r$.
2. **Constraints** (`Row`, `constraintMap`, `constraintRhs`). The linear map $G_0$ has one row for every pair $(r,V)$ with $V\in\mathcal D_r$, and
$$(G_0v)_{r,V}=\sum_{\mathbf a\,:\,(V,\mathbf a)\in\mathcal V_r}v_{r,V,\mathbf a}.$$
For an instance $x$, the right-hand side $b_x$ is given by $(b_x)_{r,V}=1$ if $V=V_{x,r}$ and $(b_x)_{r,V}=0$ otherwise. The system $G_0v=b_x$ is (27). The map $G_0$ does not depend on $x$.
3. **Restrictions** (`Hits`, `restrict`). For a proof location $u$ and a symbol $a\in\Sigma$, the vector $v^{u,a}\in F^{\mathsf m}$ keeps the coordinates $v_{r,V,\mathbf a}$ of the views with $(u_{r,j},a_j)=(u,a)$ for some $j$, and is zero in the other coordinates.
4. **The matrix $G_1$** (`Coord`, `stackMap`, `radius`). Its rows are indexed by the tuples $(r,j,a,b)$ with $r\in\{0,1\}^{\mathsf R}$, $j\in[\mathsf q]$, $a\in\Sigma$ and $b\in[B]$, and
$$(G_1v)_{r,j,a,b}=\iota\bigl(v^{u_{r,j},a}\bigr)_b .$$
So $G_1$ has $M_0=|\Sigma|\cdot Y$ rows, where $Y=B\cdot2^{\mathsf R}\cdot\mathsf q$.
5. **The code** (`code`, `padZero`). With $H=\Gamma\cdot Y+1$,
$$C=(G_1\cdot\ker G_0)\times\{0^{H}\}\subseteq F^{M_0+H}.$$
It is a linear code that does not depend on the instance.
6. **The targets** (`target`). $y_x=(G_1v_x,0^{H})$ for a solution $v_x$ of $G_0v=b_x$ if there is one, and $y_x=(0^{M_0},1^{H})$ otherwise.

The radius is $Y$: Theorem 6.4 shows that $\Delta(y_x,C)\le Y$ for the instances of the language and $\Delta(y_x,C)>\Gamma\cdot Y$ for the others.

**Formalization Note.** The paper builds $G_1$ by stacking, for every queried location $u$ and every $a\in\Sigma$, $d_u$ copies of the matrix of $v\mapsto\iota(v^{u,a})$, where $d_u$ is the number of pairs $(r,j)$ with $u_{r,j}=u$. Here the copies are indexed by these pairs, which gives the same matrix up to the order of its rows. The solution $v_x$ is picked by classical choice, so `target` is noncomputable; the distance from the target to the code does not depend on the choice. The Lean names `E`, `g`, `ρ`, `q` stand for $\iota$, $\Gamma$, $\mathsf R$, $\mathsf q$. The field $F$ is arbitrary (the paper takes it finite), $\Gamma$ is any natural number (the paper takes $\Gamma\ge2$), and `restrict` is defined for every proof location, queried or not. Computing the code and the targets in polynomial time is not formalized.""",
    "source": PAPER + r"Construction 6.2 (\label{con:pcp-reduction}), including equation (27) "
              r"(\label{eq:pcp-predicate-constraints}); Lean: LatticePrepro/PCP/Code.lean, LatticePrepro.padZero, "
              + ", ".join(NS + n for n in ("Row", "constraintMap", "constraintRhs", "Hits", "restrict",
                                           "Coord", "radius", "stackMap", "code", "target")),
})

items.append({
    "theorem_name": NS + "card_views_le",
    "theorem_title": "Theorem 6.4 (size) — the number of accepting views is at most $2^{\\mathsf R}\\cdot\\mathsf k\\cdot|\\Sigma|^{\\mathsf q}$",
    "natural_language_statement": r"""Consider a query-oblivious PCP as in Definition 6.1, with alphabet $\Sigma$, $\mathsf R$ random bits, $\mathsf q$ queries and predicate families $\mathcal D_r$, and let $\mathsf k$ be an integer with $|\mathcal D_r|\le\mathsf k$ for every random string $r$. Then the total number $\mathsf m=\sum_r|\mathcal V_r|$ of accepting views satisfies
$$\mathsf m\le2^{\mathsf R}\cdot\mathsf k\cdot|\Sigma|^{\mathsf q}.$$

This is the bound on $\mathsf m$ in the proof of Theorem 6.4 (size and time). It holds because $\mathcal V_r\subseteq\mathcal D_r\times\Sigma^{\mathsf q}$ for every $r$, and it bounds the number of variables of the accepting-view code of Construction 6.2.

**Formalization Note.** The paper takes $\mathsf k=\max_r|\mathcal D_r|$; the Lean statement allows any upper bound `K`. The number of views is `Fintype.card P.Views`, and the Lean field names `ρ`, `q` stand for $\mathsf R$, $\mathsf q$.""",
    "source": PAPER + r"proof of Theorem 6.4 (\label{thm:pcp-reduction}), size and time; "
              "Lean: LatticePrepro/PCP/Verifier.lean, " + NS + "card_views_le",
})

items.append({
    "theorem_name": NS + "card_coord",
    "theorem_title": "Theorem 6.4 (size) — the accepting-view code has block length $(|\\Sigma|+\\Gamma)\\cdot Y+1$",
    "natural_language_statement": r"""For the accepting-view code of Construction 6.2, built from a query-oblivious PCP with alphabet $\Sigma$, $\mathsf R$ random bits and $\mathsf q$ queries, an encoding map into $F^{B}$ and an integer $\Gamma\ge0$, the block length is
$$M=M_0+H=(|\Sigma|+\Gamma)\cdot Y+1,\qquad Y=B\cdot2^{\mathsf R}\cdot\mathsf q .$$
Here $M_0=|\Sigma|\cdot Y$ is the number of rows of $G_1$ and $H=\Gamma\cdot Y+1$ is the number of padding coordinates.

This is the block length stated in Theorem 6.4.

**Formalization Note.** The statement computes the cardinality of the coordinate type `P.Coord B ⊕ Fin (g * P.radius B + 1)` of the code, where `P.Coord B` is $\{0,1\}^{\mathsf R}\times[\mathsf q]\times\Sigma\times[B]$ and `P.radius B` is $Y$. It involves neither the field nor the encoding map. The Lean names `g`, `ρ`, `q` stand for $\Gamma$, $\mathsf R$, $\mathsf q$.""",
    "source": PAPER + r"Theorem 6.4 (\label{thm:pcp-reduction}), size, with step 4 of Construction 6.2 "
              r"(\label{con:pcp-reduction}); Lean: LatticePrepro/PCP/Code.lean, " + NS + "card_coord",
})

items.append({
    "theorem_name": "LatticePrepro.mul_le_sum_of_sum_prod_inv_le",
    "theorem_title": "Theorem 6.4, inequality (31) — a bound on $\\sum_r\\prod_j\\lambda_{r,j}^{-1}$ forces a large average of the $\\lambda_{r,j}$",
    "natural_language_statement": r"""Let $R$ be a finite set, let $q\ge0$ be an integer, and let $\lambda_{r,j}>0$ be real numbers for $r\in R$ and $1\le j\le q$. Let $t>0$ be a real number with
$$\Bigl(\sum_{r\in R}\prod_{j=1}^{q}\lambda_{r,j}^{-1}\Bigr)\cdot t^{q}\le|R| .$$
Then
$$|R|\cdot q\cdot t\le\sum_{r\in R}\sum_{j=1}^{q}\lambda_{r,j}.$$

In the soundness proof of Theorem 6.4, $R=\{0,1\}^{\mathsf R}$ is the set of random strings, $q=\mathsf q$, $\lambda_{r,j}=|\Lambda_{u_{r,j}}|$ is the size of the list at the $j$-th query of $r$, and $t=\mathsf s^{-1/\mathsf q}$. The hypothesis is the first inequality of (31), $\mathsf s\ge2^{-\mathsf R}\sum_r\prod_j|\Lambda_{u_{r,j}}|^{-1}$. The conclusion is $\overline\Lambda\ge\mathsf s^{-1/\mathsf q}$ for the average list size $\overline\Lambda$, which is what the other two inequalities of (31) give.

**Formalization Note.** The paper obtains the conclusion from Jensen's inequality for the exponential and then for the logarithm. The Lean proof applies $\log y\le y-1$, for each $r$, to the $q+1$ positive numbers $\lambda_{r,1}/t,\dots,\lambda_{r,q}/t$ and $t^{q}\prod_j\lambda_{r,j}^{-1}$, whose product is $1$, and sums over $r$. The statement also covers $q=0$.""",
    "source": PAPER + r"proof of Theorem 6.4 (\label{thm:pcp-reduction}), soundness, second and third "
              r"inequalities of (31) (\label{eq:pcp-list-bound}); Lean: LatticePrepro/PCP/Inequality.lean, "
              "LatticePrepro.mul_le_sum_of_sum_prod_inv_le",
})

items.append({
    "theorem_name": NS + "codeDist_le_of_mem",
    "theorem_title": "Theorem 6.4 (completeness) — $\\Delta(y_x,C)\\le Y$ for instances in the language",
    "natural_language_statement": SETUP.replace(r"$\mathsf q\ge1$ queries", r"$\mathsf q$ queries") + r""" Suppose that the PCP has perfect completeness for a language $L$: every $x\in L$ has a proof that is accepted for every random string. Then for every $x\in L$,
$$\Delta(y_x,C)\le Y .$$

This is the completeness part of Theorem 6.4. Take a proof $\pi$ that is accepted for every random string, and let $v$ be the indicator vector of the accepting views $(V_{x,r},\pi|_{I_r})$. Then $v$ satisfies the constraints (27), so $G_0v=b_x$ is solvable and $(G_1v_x,0^H)-(G_1v,0^H)$ is a codeword. The restrictions $v^{u,a}$ vanish for $a\ne\pi(u)$, so by the weight formula (29) the vector $G_1v$ has weight at most $B\cdot2^{\mathsf R}\cdot\mathsf q=Y$.

**Formalization Note.** This part needs no hypothesis on $\iota$, on $\Gamma$ or on the soundness of the PCP. $\Delta(y,C)$ is `CodeFamily.codeDist`, the minimum Hamming distance from $y$ to a codeword. """ + NAMES,
    "source": PAPER + r"Theorem 6.4 (\label{thm:pcp-reduction}), completeness; "
              "Lean: LatticePrepro/PCP/Reduction.lean, " + NS + "codeDist_le_of_mem",
})

items.append({
    "theorem_name": NS + "lt_hammingNorm_stackMap_of_solution",
    "theorem_title": "Theorem 6.4 (soundness, main step) — every solution of $G_0v=b_x$ has weight more than $\\Gamma\\cdot Y$",
    "natural_language_statement": SETUP + " " + HYPS + r"""

Then for every instance $x\notin L$ and every solution $v\in F^{\mathsf m}$ of $G_0v=b_x$, the Hamming weight $W(v)$ of $G_1v$ satisfies
$$W(v)>\Gamma\cdot Y .$$

This is the main step of the soundness proof of Theorem 6.4. A solution $v$ defines the lists $\Lambda_u=\{a\in\Sigma:v^{u,a}\ne0\}$. By the constraints (27), for every random string $r$ some accepting view $(V_{x,r},\mathbf a^{(r)})$ has a nonzero coefficient, and all its answers lie in the lists. A proof whose entries are independent and uniform in the lists is accepted for $r$ with probability at least $\prod_j|\Lambda_{u_{r,j}}|^{-1}$, so soundness gives (31), and the average list size is at least $\mathsf s^{-1/\mathsf q}$. By (29) every symbol of a list $\Lambda_u$ contributes weight at least $\delta\cdot B$ in each copy of the block of $u$, which gives $W(v)\ge\delta\cdot Y\cdot\mathsf s^{-1/\mathsf q}>\Gamma\cdot Y$.

**Formalization Note.** The random proof is replaced by a count over all proofs with entries in the lists. """ + WEAKER + r""" The exponent is a real power, `ε ^ (-(1 : ℝ) / q)`. """ + NAMES,
    "source": PAPER + r"proof of Theorem 6.4 (\label{thm:pcp-reduction}), soundness, with (28) "
              r"(\label{eq:pcp-gap}), (29) (\label{eq:pcp-weight}) and (31) (\label{eq:pcp-list-bound}); "
              "Lean: LatticePrepro/PCP/Reduction.lean, " + NS + "lt_hammingNorm_stackMap_of_solution",
})

items.append({
    "theorem_name": NS + "lt_codeDist_of_not_mem",
    "theorem_title": "Theorem 6.4 (soundness) — $\\Delta(y_x,C)>\\Gamma\\cdot Y$ for instances outside the language",
    "natural_language_statement": SETUP + " " + HYPS + r"""

Then for every instance $x\notin L$,
$$\Delta(y_x,C)>\Gamma\cdot Y .$$

This is the soundness part of Theorem 6.4. If $G_0v=b_x$ has no solution, then $y_x=(0^{M_0},1^{H})$ and every codeword vanishes on the last $H=\Gamma\cdot Y+1$ coordinates. Otherwise, by (30), the distance from $y_x$ to $C$ is the least weight of $G_1v$ over the solutions $v$ of $G_0v=b_x$, and every solution has weight more than $\Gamma\cdot Y$.

**Formalization Note.** """ + WEAKER + r""" $\Delta(y,C)$ is `CodeFamily.codeDist`, the minimum Hamming distance from $y$ to a codeword. """ + NAMES,
    "source": PAPER + r"Theorem 6.4 (\label{thm:pcp-reduction}), soundness, with (30) "
              r"(\label{eq:pcp-target-distance}); Lean: LatticePrepro/PCP/Reduction.lean, "
              + NS + "lt_codeDist_of_not_mem",
})

items.append({
    "theorem_name": NS + "pcp_reduction",
    "theorem_title": "Theorem 6.4 — reduction from query-oblivious PCPs to nearest codeword with preprocessing",
    "natural_language_statement": r"""Let a query-oblivious PCP with enumerable predicate families (Definition 6.1) be given, with alphabet $\Sigma$, $\mathsf R$ random bits, $\mathsf q\ge1$ queries and $\mathsf m$ accepting views, and let $L$ be a language for which it has perfect completeness and soundness error $\mathsf s>0$. Let $F$ be a field, let $\iota\colon F^{\mathsf m}\to F^{B}$ be an injective $F$-linear map such that every nonzero vector of the code $\iota(F^{\mathsf m})$ has Hamming weight at least $\delta\cdot B$, and let $\Gamma\ge0$ be an integer with
$$\Gamma<\delta\cdot\mathsf s^{-1/\mathsf q}.$$
Let $C$ and $y_x$ be the code and the targets of Construction 6.2, and let $Y=B\cdot2^{\mathsf R}\cdot\mathsf q$. Then:

1. **Completeness.** For every $x\in L$, $\Delta(y_x,C)\le Y$.
2. **Soundness.** For every $x\notin L$, $\Delta(y_x,C)>\Gamma\cdot Y$.
3. **Size.** The code has block length $M=(|\Sigma|+\Gamma)\cdot Y+1$.

The code $C$ depends only on the PCP, the encoding map and $\Gamma$, not on the instance. So the map $x\mapsto y_x$ sends the instances of $L$ to targets within distance $Y$ of the fixed code $C$, and all other instances to targets at distance more than $\Gamma\cdot Y$. This is the combinatorial content of the reduction from $L$ to $\Gamma$-gap nearest codeword with preprocessing over $F$.

**Formalization Note.** This is Theorem 6.4 without its running-time claims. The final sentence of the theorem, that the construction is a preprocessing reduction when the parameters are polynomial in the instance length, is therefore not formalized. """ + WEAKER + r""" Instances form an arbitrary type. The bound $\mathsf m\le2^{\mathsf R}\cdot\mathsf k\cdot|\Sigma|^{\mathsf q}$ from the proof is the separate theorem `card_views_le`. $\Delta(y,C)$ is `CodeFamily.codeDist`, and the exponent is a real power, `ε ^ (-(1 : ℝ) / q)`. """ + NAMES,
    "source": PAPER + r"Theorem 6.4 (\label{thm:pcp-reduction}); Lean: LatticePrepro/PCP/Reduction.lean, "
              + NS + "pcp_reduction",
})

for o in items:
    title = o.get("theorem_title") or o.get("definition_title")
    assert len(title) <= 200, (title, len(title))
    assert "\t" not in o["natural_language_statement"]
os.makedirs(os.path.join(P, "out", "meta"), exist_ok=True)
json.dump(items, open(os.path.join(P, "out", "meta", "batch_E.json"), "w"), indent=2, ensure_ascii=False)

milestones = [
    {"theorem_name": NS + "card_views_le",
     "milestone_title": "Theorem 6.4 (size) — number of accepting views",
     "milestone_description": r"In the proof of Theorem 6.4 (size and time): since $\mathcal V_r\subseteq\mathcal D_r\times\Sigma^{\mathsf q}$, the number of accepting views satisfies $\mathsf m\le2^{\mathsf R}\cdot\mathsf k\cdot|\Sigma|^{\mathsf q}$, where $\mathsf k=\max_r|\mathcal D_r|$ is the maximum number of predicates per random string. The milestone allows any upper bound $\mathsf k$ on the sizes $|\mathcal D_r|$."},
    {"theorem_name": "LatticePrepro.mul_le_sum_of_sum_prod_inv_le",
     "milestone_title": "Theorem 6.4, inequality (31) — the average list size",
     "milestone_description": r"In the soundness proof of Theorem 6.4, soundness of the PCP gives $\mathsf s\ge2^{-\mathsf R}\sum_r\prod_{j=1}^{\mathsf q}|\Lambda_{u_{r,j}}|^{-1}$, and two applications of Jensen's inequality give $\mathsf s\ge\overline\Lambda^{-\mathsf q}$ for the average list size $\overline\Lambda$ (31). The milestone is the passage from the first bound to the last, for arbitrary positive reals $\lambda_{r,j}$ in place of the list sizes: if $(\sum_r\prod_j\lambda_{r,j}^{-1})\cdot t^{q}\le|R|$ for some $t>0$, then $|R|\cdot q\cdot t\le\sum_r\sum_j\lambda_{r,j}$."},
    {"theorem_name": NS + "codeDist_le_of_mem",
     "milestone_title": "Theorem 6.4 (completeness) — instances in the language",
     "milestone_description": r"For Construction 6.2, if the PCP has perfect completeness, then for every $x\in\mathsf L(\mathcal R)\cap\{0,1\}^{n}$ the target satisfies $\Delta(y_x,C)\le Y$, where $Y=B\cdot2^{\mathsf R}\cdot\mathsf q$. The milestone is stated for an arbitrary language and instance set, and needs no hypothesis on the encoding map or on $\Gamma$."},
    {"theorem_name": NS + "lt_codeDist_of_not_mem",
     "milestone_title": "Theorem 6.4 (soundness) — instances outside the language",
     "milestone_description": r"For Construction 6.2, suppose that the PCP has soundness error $0<\mathsf s<1$, that $\iota$ is injective and the code $\iota(F^{\mathsf m})$ has relative distance $\delta$, and that $\Gamma<\delta\cdot\mathsf s^{-1/\mathsf q}$ (28). Then for every $x\in\{0,1\}^{n}\setminus\mathsf L(\mathcal R)$ the target satisfies $\Delta(y_x,C)>\Gamma\cdot Y$. The milestone assumes only $\mathsf s>0$ and that every nonzero codeword of $\iota(F^{\mathsf m})$ has weight at least $\delta\cdot B$."},
    {"theorem_name": NS + "pcp_reduction",
     "milestone_title": "Theorem 6.4 — the reduction from query-oblivious PCPs",
     "milestone_description": r"For Construction 6.2, suppose that the PCP has instance-independent query locations and predicate families enumerable as in Definition 6.1, perfect completeness and soundness error $0<\mathsf s<1$, that $\iota$ is injective and the code $\iota(F^{\mathsf m})$ has relative distance $\delta$, and that $\Gamma<\delta\cdot\mathsf s^{-1/\mathsf q}$. Then $\Delta(y_x,C)\le Y$ for every $x\in\mathsf L(\mathcal R)\cap\{0,1\}^{n}$, $\Delta(y_x,C)>\Gamma\cdot Y$ for every $x\in\{0,1\}^{n}\setminus\mathsf L(\mathcal R)$, and the code has block length $M=(|\Sigma|+\Gamma)\cdot Y+1$ and depends only on the PCP, the encoding map and $\Gamma$. The milestone states these three items; the running-time claims of the theorem are not formalized."},
]
json.dump(milestones, open(os.path.join(P, "mission", "milestones_s6.json"), "w"), indent=1, ensure_ascii=False)
print(f"wrote {len(items)} metadata entries and {len(milestones)} milestones")
