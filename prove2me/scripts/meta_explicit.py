#!/usr/bin/env python3
"""Write the metadata of the explicit-construction items (LatticePrepro/Explicit.lean and the
extension bundles it needs): out/meta/batch_F.json and mission/milestones_explicit.json.

  python3 meta_explicit.py
"""
import json
import os

P = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAPER = ("G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing "
         "(STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), ")
LP = "LatticePrepro."

TABLES = r"""Let $p$ be a prime and let $V$ be a quadratic verifier over $\mathbb F_p$ with instance length $n$, $S$ assignment coordinates, $N$ evaluation tables and language $L(V)\subseteq\{0,1\}^n$. For a gap exponent $\delta<1$ put $m=\lceil\delta/(1-\delta)\rceil+1$ (`momentAxes`) and $g=(S+1)^{k}$ with $k$ = `gapExp p δ`. **Tables** for $V$ and $\delta$ consist of an integer $B\ge2$ with $8Ng\le B^{m}\le2^{m}\cdot8Ng$ and an explicit moment representation in the sense of Theorem A.8 with $m$ axes and representation bound $r=B^{m}$. They do not depend on the instance."""

SYSTEM = r"""The **fixed linear system** of the tables $T$ is the system $Av=b_x$ of Construction 4.5 built from them: $A$ is a fixed $\mathbb F_p$-linear map on $\mathbb F_p^{N_{\mathrm{col}}}$ whose columns are partitioned into $D$ blocks of size $b$, and the right-hand side $b_x$, for $x\in\{0,1\}^n$, is zero except for the entries $\theta_x^{k}$ of the translation equations, where $\theta_x$ is the encoding of the instance."""

WHY = r"""The existence form of this statement only asserts that some code or lattice with targets has the gap. Since the Lean statement does not require the targets to be computable, that form is satisfied by a construction unrelated to the paper, in which the target records whether $x$ is in the language. Here the code, the lattice and the targets are the ones the paper constructs."""

NOTFORM = r"""Polynomial-time computability of the code, the lattice and the targets is not formalized. The target uses a solution of $Av=b_x$ picked by classical choice, where the paper uses Gaussian elimination; the distance from the target to the code does not depend on the solution."""

items = []

# ------------------------------------------------------------------ definition bundles

items.append({
    "definition_name": "LatticePrepro_Conversions_Codes_Ext",
    "definition_title": "The code family of a block-sparse linear system over the prime field (Lemma 3.11)",
    "natural_language_statement": r"""This bundle adds one definition to the code side of Lemma 3.11.

**The code family of a linear system** (`LinearSystemFamily.toCodeFamily`). Let $L$ be a linear-system family over $\mathbb F_p$: a fixed linear map $A$ on $\mathbb F_p^{\iota}$ for a finite column set $\iota$, right-hand sides $b_x$, and a partition of the columns into $D$ blocks of size $b$. Its code family has coordinate set $\iota\sqcup\iota$, the code
$$\mathcal C_L=\ker A\times\{0\}\subseteq\mathbb F_p^{\iota\sqcup\iota},$$
and the targets $y_x=(v_x,0)$ for a solution $v_x$ of $Av=b_x$ if the system is solvable, and $y_x=(0,\mathbf 1)$ otherwise.

The bundle also contains the lemma that each of the $2D$ blocks of the coordinate set $\iota\sqcup\iota$ has exactly $b$ elements (`card_codeBlk_fiber`).

This packages the code `LinearSystemFamily.code` and the targets `LinearSystemFamily.codeTarget` of the proof of Lemma 3.11 (Appendix B.1) as a `CodeFamily`.

**Formalization Note.** The solution $v_x$ is picked by classical choice, so the family is noncomputable; the distance from $y_x$ to the code does not depend on the choice.""",
    "source": PAPER + r"proof of Lemma 3.11 (\label{lem:block-system-codes}) in Appendix B.1 "
              r"(\label{subsec:affine-code-proof}); Lean: LatticePrepro/Conversions/Codes.lean, "
              + LP + "LinearSystemFamily.toCodeFamily, " + LP + "LinearSystemFamily.card_codeBlk_fiber",
})

items.append({
    "definition_name": "LatticePrepro_Conversions_ConstructionA_Ext",
    "definition_title": "Construction A lattices and reduction modulo $p$ (Lemma B.1)",
    "natural_language_statement": r"""Fix a prime $p$ and a coordinate set $M$.

1. **Reduction modulo $p$** (`redMod`): the $\mathbb Z$-linear map $\mathbb Z^{M}\to\mathbb F_p^{M}$ that reduces every coordinate modulo $p$.
2. **Construction A** (`constructionA`): for a linear code $\mathcal C\subseteq\mathbb F_p^{M}$, the lattice
$$\Lambda_{\mathcal C}=\{v\in\mathbb Z^{M}: v \bmod p\in\mathcal C\}=\mathcal C+p\,\mathbb Z^{M}.$$

The bundle also contains two rewriting lemmas: the coordinates of the reduction (`redMod_apply`), and that the canonical lift of a word $y\in\mathbb F_p^{M}$ (with entries in $\{0,\dots,p-1\}$, `liftZMod`) reduces to $y$ (`redMod_liftZMod`).

This is the lattice of Lemma B.1, used in the lattice reduction of Lemma 3.12.

**Formalization Note.** `constructionA C` is a `Submodule ℤ (M → ℤ)`, defined as the preimage of $\mathcal C$, regarded as an additive subgroup, under reduction modulo $p$.""",
    "source": PAPER + r"Lemma B.1 (\label{lem:construction-a-gap}) in Appendix B.2 "
              r"(\label{subsec:conversion-proof}); Lean: LatticePrepro/Conversions/ConstructionA.lean, "
              + LP + "redMod, " + LP + "constructionA",
})

items.append({
    "definition_name": "LatticePrepro_Conversions_Hadamard_Ext",
    "definition_title": "The blockwise Walsh–Hadamard transform as a linear map (Lemma B.2)",
    "natural_language_statement": r"""Fix $k\ge0$ and a set $\beta$ of blocks. Coordinates are pairs $(s,u)$ of a block $s\in\beta$ and a position $u\in\mathbb F_2^{k}$, and $H_k$ is the $2^{k}\times2^{k}$ Walsh–Hadamard matrix with entries $(-1)^{\langle u,w\rangle}$.

**The blockwise transform** (`Hadamard.blockHadₗ`) is the $\mathbb Z$-linear map on $\mathbb Z^{\beta\times\mathbb F_2^{k}}$ that applies $H_k$ inside every block:
$$(Hv)_{(s,u)}=\sum_{w\in\mathbb F_2^{k}}(-1)^{\langle u,w\rangle}\,v_{(s,w)}.$$
It is the function `Hadamard.blockHad` as a linear map.

The bundle also contains the lemmas that make it one: $|\mathbb F_2^{k}|=2^{k}$ (`card_Idx`), the displayed formula (`blockHad_apply`), additivity and homogeneity (`blockHad_add`, `blockHad_smul`).

This is the transform of Lemma B.2, which spreads a vector with one nonzero entry per block over its block; Lemma 3.12 applies it to the Construction A lattice when $p>2$.""",
    "source": PAPER + r"Lemma B.2 (\label{lem:embeddings}) in Appendix B.2 "
              r"(\label{subsec:conversion-proof}); Lean: LatticePrepro/Conversions/Hadamard.lean, "
              + LP + "Hadamard.blockHadₗ",
})

items.append({
    "definition_name": "LatticePrepro_Conversions_Padding",
    "definition_title": "Padding a word by zero coordinates along an injection (proof of Lemma 3.12)",
    "natural_language_statement": r"""Let $f\colon\iota\hookrightarrow M$ be an injection of coordinate sets and $F$ a semiring.

**Padding** (`padMap f`) is the $F$-linear map $F^{\iota}\to F^{M}$ that extends a word by zeros:
$$(\operatorname{pad}_f y)_{m}=\begin{cases}y_i,&m=f(i),\\0,&m\notin f(\iota).\end{cases}$$

In the proof of Lemma 3.12 (Appendix B.3) every block of the code of Lemma 3.11 is padded in this way to a size that is a power of two, so that the Walsh–Hadamard transform can be applied blockwise.

**Formalization Note.** The preimage of $m$ is picked by classical choice; it is unique because $f$ is injective.""",
    "source": PAPER + r"proof of Lemma 3.12 (\label{lem:block-system-lattices}) in Appendix B.3 "
              r"(\label{subsec:gap-search-proof}); Lean: LatticePrepro/Conversions/Padding.lean, "
              + LP + "padMap",
})

items.append({
    "definition_name": "LatticePrepro_Conversions_Lattices_Ext",
    "definition_title": "The padded code and the two lattices of Lemma 3.12",
    "natural_language_statement": r"""Let $L$ be a linear-system family over $\mathbb F_p$ with $D$ blocks of size $b$, and let $\mathcal C_L\subseteq\mathbb F_p^{\iota\sqcup\iota}$ and $y_x$ be its code and targets (Lemma 3.11), with $2D$ blocks of size $b$. These definitions build the lattices of Lemma 3.12.

1. **Padded block size** (`padK`, `PadIdx`, `PadM`). $k=\lceil\log_2 b\rceil$, so that $b\le2^{k}<2b$. The padded coordinate set consists of the pairs of one of the $2D$ blocks and a position in $\mathbb F_2^{k}$; it has $M=2D\cdot2^{k}$ elements.
2. **Padding embedding** (`codeEnum`, `codeRank`, `padIdxEquiv`, `padEmbFn`, `padEmb`). An enumeration of the code coordinates gives every coordinate its rank inside its block, a number below $b$. The embedding sends a coordinate to the pair of its block and the position with that rank, for a fixed bijection between $\{0,\dots,2^{k}-1\}$ and $\mathbb F_2^{k}$. It is injective and maps blocks into blocks.
3. **Padded code and targets** (`padCode`, `padTarget`). $\mathcal C_{\mathrm{pad}}$ is the image of $\mathcal C_L$ under extension by zero along the embedding, and $y^{\mathrm{pad}}_x$ is the image of $y_x$.
4. **The Construction A lattice** (`latticeA`). $\Lambda_A=\{v\in\mathbb Z^{M}:v\bmod p\in\mathcal C_{\mathrm{pad}}\}$, with the target $t_x\in\{0,\dots,p-1\}^{M}$ that lifts $y^{\mathrm{pad}}_x$.
5. **The transformed lattice** (`latticeH`). $\Lambda_H=H\Lambda_A$ with the target $Ht_x$, where $H$ is the blockwise Walsh–Hadamard transform.

The bundle also contains the lemmas needed for these definitions: $b\le2^{k}$, the rank is below $b$, the rank is strictly increasing and injective inside a block, and the embedding is injective.

Lemma 3.12 uses $\Lambda_A$ for norm exponents $p\le2$ and $\Lambda_H$ for $p>2$ and $p=\infty$.

**Formalization Note.** The enumeration of the coordinates and the bijection with $\mathbb F_2^{k}$ are picked by classical choice; the statements proved about these lattices hold for every choice.""",
    "source": PAPER + r"proof of Lemma 3.12 (\label{lem:block-system-lattices}) in Appendix B.3 "
              r"(\label{subsec:gap-search-proof}); Lean: LatticePrepro/Conversions/Lattices.lean, "
              + ", ".join(LP + "LinearSystemFamily." + n for n in (
                  "padK", "PadIdx", "PadM", "codeEnum", "codeRank", "padIdxEquiv", "padEmbFn",
                  "padEmb", "padCode", "padTarget", "latticeA", "latticeH")),
})

items.append({
    "definition_name": "LatticePrepro_ThreeSAT_Ext",
    "definition_title": "The quadratic verifier for 3SAT (proof of Theorem 5.1)",
    "natural_language_statement": r"""**The 3SAT verifier** (`ThreeSAT.verifier p v`). For a prime $p$ and a number $v$ of variables, this is the quadratic verifier over $\mathbb F_p$ obtained from the 3SAT verifier circuit `ThreeSAT.circuit v` by reading the circuit as a gate verifier (Definitions 3.13–3.14) and replacing its gates by quadratic gate equations (Claim 3.15).

Its instances are the bit strings of length $n=(2v)^{3}$, one bit for each possible clause, and its language is the set of encodings of satisfiable 3SAT instances on $v$ variables.

This is the verifier $V_n$ in the proof of Theorem 5.1.""",
    "source": PAPER + r"proof of Theorem 5.1 (\label{thm:approximation-hardness}), with Definitions "
              r"3.13–3.14 (\label{def:verifier}, \label{def:computation-assignment}) and Claim 3.15 "
              r"(\label{clm:verifier-system}); Lean: LatticePrepro/ThreeSAT.lean, " + LP + "ThreeSAT.verifier",
})

items.append({
    "definition_name": "LatticePrepro_Explicit",
    "definition_title": "Theorem 5.1 for the paper's construction: tables, the code and lattice built from them, and the gap property",
    "natural_language_statement": r"""These definitions name the code and the lattice that the paper constructs for Theorem 5.1, so that the theorem can be stated for them.

1. **Gap of a code family** (`CodeFamily.HasGap`). A code family with code $\mathcal C\subseteq F^{M}$ and targets $t_x$ has the gap for a radius $R$, a real $\varepsilon$, a language $\mathrm{Lang}$ and integers $n,C$ if $R\ge1$, $1\le M\le n^{C}$, $\Delta(t_x,\mathcal C)\le R$ for $x\in\mathrm{Lang}$, and $\Delta(t_x,\mathcal C)>M^{1-\varepsilon}\cdot R$ for $x\notin\mathrm{Lang}$.
2. **Gap of a lattice family** (`LatticeFamily.HasGap`). A lattice family with lattice $\Lambda\subseteq\mathbb Z^{M}$ and targets $t_x$ has the gap for a norm exponent $p$ (with $s=\min\{p,2\}$), a radius $R$, $\varepsilon$, $\mathrm{Lang}$ and $n,C$ if $R\ge1$, $1\le M\le n^{C}$, $N\cdot\mathbb Z^{M}\subseteq\Lambda$ for some integer $N>0$, $\operatorname{dist}_p(t_x,\Lambda)\le R$ for $x\in\mathrm{Lang}$, and $\operatorname{dist}_p(t_x,\Lambda)>M^{1/s-\varepsilon}\cdot R$ for $x\notin\mathrm{Lang}$.
3. **Change of instances** (`CodeFamily.comap`, `LatticeFamily.comap`). The same code or lattice, with the target of $y$ defined as the target of $f(y)$ for a map $f$ of instances.
4. **The code of a linear system over $F$** (`LinearSystemFamily.codeFamily`). For a linear-system family over $\mathbb F_p$ and a field $F$ of characteristic $p$: the code spanned over $F$ by $\ker A\times\{0\}$, with the targets of Lemma 3.11 read in $F$.
5. **The lattice and radius of a linear system** (`LinearSystemFamily.latticeFamily`, `latticeRadius`). For a norm exponent $p$: the Construction A lattice $\Lambda_A$ of the padded code if $p\le2$, and its blockwise Walsh–Hadamard transform $\Lambda_H$ if $p>2$ or $p=\infty$, with their targets. The radius is $\lceil D^{1/p}\rceil$ for $p\le2$, $\lceil(2^{k}D)^{1/p}\rceil$ for $2<p<\infty$, and $1$ for $p=\infty$, where $D$ is the number of blocks and $2^{k}$ the padded block size.
6. **Tables** (`QuadraticVerifier.Tables`). """ + TABLES.replace("Let $p$ be a prime and let $V$ be", "Let $V$ be") + r"""
7. **The fixed linear system, code and lattice of the tables** (`Tables.system`, `Tables.codeFamily`, `Tables.latticeFamily`, `Tables.latticeRadius`). The system is $Av=b_x$ of Construction 4.5 for the tables. The code family, the lattice family and the radius are those of items 4 and 5 for this system.

Theorem 5.1 is then the statement that `Tables.codeFamily` and `Tables.latticeFamily` have the gap for the language of the verifier.

**Formalization Note.** `HasGap` has the same content as the fields of `CodeGap` and `LatticeGap`, but as a property of a given family instead of an existence statement. """ + WHY + " " + NOTFORM + r""" The case distinction on $p\le2$ uses the classical decidability of the order on the reals.""",
    "source": PAPER + r"Theorem 5.1 (\label{thm:approximation-hardness}) and its proof, with Construction "
              r"4.5 (\label{con:fixed-verifier}), Lemma 3.11 (\label{lem:block-system-codes}), Lemma 3.12 "
              r"(\label{lem:block-system-lattices}), Theorem 4.8 (\label{thm:quantitative-affine-gap}) and "
              r"Theorem A.8 (\label{thm:moment-representation-construction}); Lean: LatticePrepro/Explicit.lean, "
              + ", ".join(LP + n for n in (
                  "CodeFamily.HasGap", "LatticeFamily.HasGap", "CodeFamily.comap", "LatticeFamily.comap",
                  "LinearSystemFamily.codeFamily", "LinearSystemFamily.latticeFamily",
                  "LinearSystemFamily.latticeRadius", "QuadraticVerifier.Tables",
                  "QuadraticVerifier.Tables.system", "QuadraticVerifier.Tables.codeFamily",
                  "QuadraticVerifier.Tables.latticeFamily", "QuadraticVerifier.Tables.latticeRadius")),
})

# ------------------------------------------------------------------ theorems

T = LP + "QuadraticVerifier.Tables."

items.append({
    "theorem_name": LP + "LinearSystemFamily.exists_latticeReduction_eq",
    "theorem_title": "Lemma 3.12 for the paper's lattice — the reduction is realized by Construction A and its Walsh–Hadamard transform",
    "natural_language_statement": r"""Let $L$ be a linear-system family over $\mathbb F_p$ with $D\ge1$ blocks of size $b$, let $g<b$ be an integer, and let $p'\ge1$ be a real norm exponent or $p'=\infty$, with $s=\min\{p',2\}$. Let $\Lambda$ be the lattice of the paper for $L$ and $p'$: the Construction A lattice of the padded code if $p'\le2$, and its blockwise Walsh–Hadamard transform otherwise, with its integer targets $t_x$. Let $R$ be the radius $\lceil D^{1/p'}\rceil$ for $p'\le2$, $\lceil(2^{k}D)^{1/p'}\rceil$ for $2<p'<\infty$, and $1$ for $p'=\infty$, where $2^{k}$ is the padded block size.

Then $\Lambda$ and $R$ are the lattice and the radius of a lattice reduction in the sense of Lemma 3.12. That is, with $n$ the number of columns of $L$ and $M$ the dimension of $\Lambda$:

- $2n\le M<4n$, $1\le R\le M$, and $N\cdot\mathbb Z^{M}\subseteq\Lambda$ for some integer $N>0$;
- for every YES instance $x$ there is $v\in\Lambda$ with $\|t_x-v\|_{p'}\le R$;
- there is a residual weight $w(x,v)\in\mathbb N$ with $w(x,v)\le16\cdot D\cdot(\|t_x-v\|_{p'}/R)^{s}$ for all $x$ and all $v\in\Lambda$, and $w(x,v)>g\cdot D$ for every NO instance $x$ and all $v\in\Lambda$.

This is Lemma 3.12 with the lattice named. The existence form (`exists_latticeReduction`) asserts that some lattice reduction exists; this statement says which lattice and radius it uses.

**Formalization Note.** The conclusion is the existence of a `LatticeReduction` whose lattice family equals `L.latticeFamily` and whose radius equals `L.latticeRadius`. The statement holds for every real $p'\ge1$ (the paper takes $p'$ rational). Computability of the lattice basis, of the targets and of the residual weight is not formalized.""",
    "source": PAPER + r"Lemma 3.12 (\label{lem:block-system-lattices}) and its proof in Appendix B.3 "
              r"(\label{subsec:gap-search-proof}); Lean: LatticePrepro/Explicit.lean, "
              + LP + "LinearSystemFamily.exists_latticeReduction_eq",
})

items.append({
    "theorem_name": T + "nonempty",
    "theorem_title": "Theorem 4.8 (choice of parameters) and Theorem A.8 — tables exist for every verifier",
    "natural_language_statement": TABLES + r"""

**Statement.** If $S\ge2$ and $\delta<1$, then tables for $V$ and $\delta$ exist.

The base $B$ is the one chosen in the proof of Theorem 4.8 (the least $B\ge2$ with $B^{m}\ge8Ng$), and the moment representation is the one of Theorem A.8 for the parameters $S$, $m$ and $B$.

**Formalization Note.** The conclusion is `Nonempty (V.Tables δ)`. The hypothesis $S\ge2$ is the one of Theorem A.8; it holds for the 3SAT verifier.""",
    "source": PAPER + r"proof of Theorem 4.8 (\label{thm:quantitative-affine-gap}), choice of the base, and "
              r"Theorem A.8 (\label{thm:moment-representation-construction}); "
              "Lean: LatticePrepro/Explicit.lean, " + T + "nonempty",
})

items.append({
    "theorem_name": T + "system_spec",
    "theorem_title": "Theorem 4.8 for the fixed linear system of Construction 4.5 — gap reduction and size bound",
    "natural_language_statement": TABLES + "\n\n" + SYSTEM + r"""

**Statement.** Let $\delta<1$ and let $T$ be tables for $V$ and $\delta$. Then the fixed linear system of $T$ satisfies:

1. **Completeness.** For every $x\in L(V)$, the system $Av=b_x$ has a solution $v\in\{0,1\}^{N_{\mathrm{col}}}$ with at most one nonzero coordinate in each block.
2. **Soundness.** For every $x\notin L(V)$, every solution of $Av=b_x$ has Hamming weight more than $g\cdot D$.
3. $g<b$ and $D\ge1$.
4. **Size.** $N_{\mathrm{col}}^{\,m}\le\bigl(8\,p^{4}\,m\,(S+1)\bigr)^{(m+7)m}\cdot g^{m+1}$.

This is Theorem 4.8 for the system the paper constructs. The existence form (`exists_gapReduction`) asserts that some linear system family has these properties; here the system is the one of Construction 4.5, and the statement holds for every choice of tables.

**Formalization Note.** Items 1 and 2 are `IsGapReduction`. The size bound is the bound (22) raised to the $m$-th power. The running-time claims of Theorem 4.8 are not formalized.""",
    "source": PAPER + r"Theorem 4.8 (\label{thm:quantitative-affine-gap}) with Construction 4.5 "
              r"(\label{con:fixed-verifier}) and Theorem 4.6 (\label{thm:fixed-verifier-reduction}); "
              "Lean: LatticePrepro/Explicit.lean, " + T + "system_spec",
})

items.append({
    "theorem_name": T + "codeFamily_hasGap",
    "theorem_title": "Theorem 5.1 (codes) for the paper's code — the code $\\ker A\\times\\{0\\}$ of the fixed linear system has gap $M^{1-\\varepsilon}$",
    "natural_language_statement": TABLES + "\n\n" + SYSTEM + r"""

**Statement.** Let $F$ be a field of characteristic $p$, let $0<\varepsilon<1$, and let $T$ be tables for $V$ and $\delta=1-\varepsilon$. Let $\mathcal C\subseteq F^{M}$, $M=2N_{\mathrm{col}}$, be the code spanned over $F$ by $\ker A\times\{0\}$, with the targets $t_x=(v_x,0)$ for a solution $v_x$ of $Av=b_x$ if there is one and $t_x=(0,\mathbf 1)$ otherwise. Then, with $C$ = `sizeExp p (1 - ε)`,
$$1\le M\le(S+1)^{C},\qquad D\ge1,$$
$$x\in L(V)\ \Longrightarrow\ \Delta(t_x,\mathcal C)\le D,\qquad x\notin L(V)\ \Longrightarrow\ \Delta(t_x,\mathcal C)>M^{1-\varepsilon}\cdot D .$$

This is Theorem 5.1 for codes, for an arbitrary quadratic verifier, with the radius $R=D$. """ + WHY + r"""

**Formalization Note.** The statement holds for every choice of tables; they exist by `Tables.nonempty`. The conclusion is `CodeFamily.HasGap`. The field $F$ is any field that is an $\mathbb F_p$-algebra (the paper takes it finite). """ + NOTFORM,
    "source": PAPER + r"Theorem 5.1 (\label{thm:approximation-hardness}), code case, with Lemma 3.11 "
              r"(\label{lem:block-system-codes}) and Construction 4.5 (\label{con:fixed-verifier}); "
              "Lean: LatticePrepro/Explicit.lean, " + T + "codeFamily_hasGap",
})

LATT = r"""Let $p'\ge1$ be a real norm exponent or $p'=\infty$, with $s=\min\{p',2\}$, and let $0<\varepsilon<1/s$. Let $V$ be a quadratic verifier over $\mathbb F_2$ with instance length $n$, $S$ assignment coordinates and language $L(V)$, and let $T$ be tables for $V$ and the gap exponent $\delta=1-s\varepsilon$ (a base and an explicit moment representation, independent of the instance). Let $Av=b_x$ be the fixed linear system of Construction 4.5 for $T$, with $D$ blocks, let $\Lambda\subseteq\mathbb Z^{M}$ be the lattice of Lemma 3.12 for this system (the Construction A lattice of the padded code $\ker A\times\{0\}$ if $p'\le2$, its blockwise Walsh–Hadamard transform otherwise), with its integer targets $t_x$, and let $R$ be the radius of Lemma 3.12 ($\lceil D^{1/p'}\rceil$, $\lceil(2^{k}D)^{1/p'}\rceil$ or $1$)."""

LATT_CONCL = r"""$$1\le M\le(S+1)^{C},\qquad R\ge1,\qquad N\cdot\mathbb Z^{M}\subseteq\Lambda\ \text{for some integer }N>0,$$
$$x\in L(V)\ \Longrightarrow\ \operatorname{dist}_{p'}(t_x,\Lambda)\le R,\qquad x\notin L(V)\ \Longrightarrow\ \operatorname{dist}_{p'}(t_x,\Lambda)>M^{1/s-\varepsilon}\cdot R .$$"""

items.append({
    "theorem_name": T + "latticeFamily_hasGap_of_eq",
    "theorem_title": "Theorem 5.1 (lattices) for the paper's lattice, with the gap exponent $\\delta=1-s\\varepsilon$ as a variable",
    "natural_language_statement": LATT.replace(r"and the gap exponent $\delta=1-s\varepsilon$", r"and a real number $\delta$ with $\delta=1-s\varepsilon$") + r"""

**Statement.** With $C$ = `sizeExp 2 δ`,
""" + LATT_CONCL + r"""

This is the statement `Tables.latticeFamily_hasGap` with the exponent $\delta$ kept as a variable that is assumed equal to $1-s\varepsilon$. It carries the proof; the stated form of Theorem 5.1 for lattices follows by substituting $\delta$.

**Formalization Note.** The conclusion is `LatticeFamily.HasGap`. """ + NOTFORM.replace("the code, the lattice and the targets", "the lattice and the targets").replace("to the code", "to the lattice"),
    "source": PAPER + r"Theorem 5.1 (\label{thm:approximation-hardness}), lattice case, with Lemma 3.12 "
              r"(\label{lem:block-system-lattices}); Lean: LatticePrepro/Explicit.lean, "
              + T + "latticeFamily_hasGap_of_eq",
})

items.append({
    "theorem_name": T + "latticeFamily_hasGap",
    "theorem_title": "Theorem 5.1 (lattices) for the paper's lattice — the lattice of Lemma 3.12 for the fixed linear system has gap $M^{1/s-\\varepsilon}$",
    "natural_language_statement": LATT + r"""

**Statement.** With $C$ = `sizeExp 2 (1 - s ε)`,
""" + LATT_CONCL + r"""

This is Theorem 5.1 for lattices, for an arbitrary quadratic verifier over $\mathbb F_2$. """ + WHY + r"""

**Formalization Note.** The statement holds for every choice of tables; they exist by `Tables.nonempty`. The conclusion is `LatticeFamily.HasGap`. The exponent $p'$ ranges over all reals $p'\ge1$ and $\infty$ (the paper takes $p'$ rational). """ + NOTFORM.replace("the code, the lattice and the targets", "the lattice and the targets").replace("to the code", "to the lattice"),
    "source": PAPER + r"Theorem 5.1 (\label{thm:approximation-hardness}), lattice case, with Lemma 3.12 "
              r"(\label{lem:block-system-lattices}) and Construction 4.5 (\label{con:fixed-verifier}); "
              "Lean: LatticePrepro/Explicit.lean, " + T + "latticeFamily_hasGap",
})

SAT_SETUP = r"""Instances of 3SAT on $v$ variables are encoded as bit strings of length $n=(2v)^{3}$, one bit per possible clause, and $V_v$ is the quadratic verifier of the 3SAT verifier circuit over the relevant prime field. Tables for $V_v$ consist of a base and an explicit moment representation (Theorem A.8) in the ranges of the proof of Theorem 4.8; they do not depend on the instance."""

CODE3 = r"""**Codes.** For every prime $p$, every finite field $F$ of characteristic $p$ and every $0<\varepsilon<1$, there is $C\in\mathbb N$ such that for every $v\ge1$ there are tables $T$ for $V_v$ over $\mathbb F_p$ for which the following holds. Let $Av=b_x$ be the fixed linear system of Construction 4.5 for $T$, with $D$ blocks, and let $\mathcal C\subseteq F^{M}$ be the code spanned over $F$ by $\ker A\times\{0\}$, with the targets $t_x$ of Lemma 3.11. Then $1\le M\le n^{C}$, $D\ge1$, and
$$x\ \text{satisfiable}\ \Longrightarrow\ \Delta(t_x,\mathcal C)\le D,\qquad x\ \text{unsatisfiable}\ \Longrightarrow\ \Delta(t_x,\mathcal C)>M^{1-\varepsilon}\cdot D .$$"""

LAT3 = r"""**Lattices.** For every real $p'\ge1$ or $p'=\infty$, with $s=\min\{p',2\}$, and every $0<\varepsilon<1/s$, there is $C\in\mathbb N$ such that for every $v\ge1$ there are tables $T$ for $V_v$ over $\mathbb F_2$ for which the following holds. Let $\Lambda\subseteq\mathbb Z^{M}$ be the lattice of Lemma 3.12 for the fixed linear system of $T$, with its integer targets $t_x$ and its radius $R$. Then $1\le M\le n^{C}$, $R\ge1$, $N\cdot\mathbb Z^{M}\subseteq\Lambda$ for some integer $N>0$, and
$$x\ \text{satisfiable}\ \Longrightarrow\ \operatorname{dist}_{p'}(t_x,\Lambda)\le R,\qquad x\ \text{unsatisfiable}\ \Longrightarrow\ \operatorname{dist}_{p'}(t_x,\Lambda)>M^{1/s-\varepsilon}\cdot R .$$"""

NOTE3 = (r"""**Formalization Note.** Only the tables are asserted to exist; the code, the lattice, the targets and the radius are defined from them, and the instance enters through the right-hand side $b_x$ of the fixed linear system alone. """
         + NOTFORM + r""" The description lengths of Theorem 5.1 are not formalized either.""")

items.append({
    "theorem_name": LP + "ThreeSAT.explicit_code_gap",
    "theorem_title": "Theorem 5.1 (codes, 3SAT) for the paper's code — gap $M^{1-\\varepsilon}$ with $M\\le n^{C}$",
    "natural_language_statement": SAT_SETUP + "\n\n" + CODE3 + r"""

This is the code half of Theorem 5.1 for the code that the paper constructs. """ + WHY + "\n\n" + NOTE3,
    "source": PAPER + r"Theorem 5.1 (\label{thm:approximation-hardness}), codes, for the 3SAT verifier; "
              "Lean: LatticePrepro/Explicit.lean, " + LP + "ThreeSAT.explicit_code_gap",
})

items.append({
    "theorem_name": LP + "ThreeSAT.explicit_lattice_gap",
    "theorem_title": "Theorem 5.1 (lattices, 3SAT) for the paper's lattice — gap $M^{1/s-\\varepsilon}$ with $M\\le n^{C}$",
    "natural_language_statement": SAT_SETUP + "\n\n" + LAT3 + r"""

This is the lattice half of Theorem 5.1 for the lattice that the paper constructs. """ + WHY + "\n\n" + NOTE3,
    "source": PAPER + r"Theorem 5.1 (\label{thm:approximation-hardness}), lattices, for the 3SAT verifier; "
              "Lean: LatticePrepro/Explicit.lean, " + LP + "ThreeSAT.explicit_lattice_gap",
})

items.append({
    "theorem_name": LP + "ThreeSAT.explicit_code_and_lattice_gaps",
    "theorem_title": "Theorem 5.1 (fixed code and lattice gaps) for 3SAT, for the code and the lattice of the paper — both parts",
    "natural_language_statement": SAT_SETUP + r""" Both of the following hold.

1. """ + CODE3 + r"""

2. """ + LAT3 + r"""

This is the paper's Theorem 5.1 for the 3SAT verifier, stated for the code and the lattice that the paper constructs; it is the conjunction of `ThreeSAT.explicit_code_gap` and `ThreeSAT.explicit_lattice_gap`. """ + WHY + "\n\n" + NOTE3 + r""" The exponent $p'$ ranges over all reals $p'\ge1$ and $\infty$ (the paper takes it rational), and $M^{\,\cdot}$ is a real power.""",
    "source": PAPER + r"Theorem 5.1 (\label{thm:approximation-hardness}) for the 3SAT verifier, with "
              r"Construction 4.5 (\label{con:fixed-verifier}), Lemma 3.11 (\label{lem:block-system-codes}) "
              r"and Lemma 3.12 (\label{lem:block-system-lattices}); Lean: LatticePrepro/Explicit.lean, "
              + LP + "ThreeSAT.explicit_code_and_lattice_gaps",
})

for o in items:
    title = o.get("theorem_title") or o.get("definition_title")
    assert len(title) <= 200, (title, len(title))
    assert "\t" not in o["natural_language_statement"]
os.makedirs(os.path.join(P, "out", "meta"), exist_ok=True)
json.dump(items, open(os.path.join(P, "out", "meta", "batch_F.json"), "w"), indent=2, ensure_ascii=False)

EXPL = (r" The milestone is stated for the code and lattice that the paper constructs, so it cannot "
        r"be met by a construction whose targets depend on the instance in an arbitrary way; "
        r"polynomial-time computability is not formalized.")
milestones = [
    {"theorem_name": T + "nonempty",
     "milestone_title": "Theorem 4.8 (choice of parameters) — tables exist",
     "milestone_description": r"The proof of Theorem 4.8 chooses a base $B\ge2$ with $8Ng\le B^{m}\le2^{m}\cdot8Ng$ and applies Theorem A.8 to obtain an explicit moment representation with $m$ axes and representation bound $B^{m}$. The milestone states that this instance-independent data (the tables) exists for every verifier with $S\ge2$ assignment coordinates and every gap exponent $\delta<1$."},
    {"theorem_name": T + "system_spec",
     "milestone_title": "Theorem 4.8 — the fixed linear system of Construction 4.5 (explicit form)",
     "milestone_description": r"For a prime $p$, a verifier $V$ with $S$ coordinates and integers $g,m\ge1$, there is a preprocessing reduction from $L(V)$ to block-sparse linear systems over $\mathbb F_p$ with gap $g$ whose matrix has $n\le(8p^{4}m(S+1))^{m+7}g^{1+1/m}$ columns (22). The milestone states this for the linear system of Construction 4.5 itself, for every choice of tables: completeness, soundness with gap $g$, $g<b$, at least one block, and the bound $n^{m}\le(8p^{4}m(S+1))^{(m+7)m}g^{m+1}$."},
    {"theorem_name": LP + "LinearSystemFamily.exists_latticeReduction_eq",
     "milestone_title": "Lemma 3.12 — the lattice reduction for the paper's lattice (explicit form)",
     "milestone_description": r"Lemma 3.12 gives a full-rank lattice $\Lambda\subseteq\mathbb Z^{M}$ with $2Db\le M<4Db$, integer targets, an integer radius $1\le R\le M$ and a weight $w$ with $w\le16D(\|t-v\|_p/R)^{s}$ for all instances and $w>gD$ for NO instances. The milestone states that these properties hold for the lattice of the proof: the Construction A lattice of the padded code for $p\le2$ and its blockwise Walsh–Hadamard transform for $p>2$ and $p=\infty$, with the radius $\lceil D^{1/p}\rceil$, $\lceil(2^{k}D)^{1/p}\rceil$ or $1$."},
    {"theorem_name": T + "codeFamily_hasGap",
     "milestone_title": "Theorem 5.1 (codes) — the paper's code for any quadratic verifier",
     "milestone_description": r"Theorem 5.1 for codes, with the code named: for every field $F$ of characteristic $p$, every $0<\varepsilon<1$, every quadratic verifier $V$ and every choice of tables, the code $\ker A\times\{0\}$ of the fixed linear system of Construction 4.5 (extended to $F$) with the targets of Lemma 3.11 has block length $M\le(S+1)^{C}$, and $x\in L(V)$ implies $\Delta(t_x,\mathcal C)\le D$ while $x\notin L(V)$ implies $\Delta(t_x,\mathcal C)>M^{1-\varepsilon}\cdot D$, where $D$ is the number of blocks." + EXPL},
    {"theorem_name": T + "latticeFamily_hasGap",
     "milestone_title": "Theorem 5.1 (lattices) — the paper's lattice for any quadratic verifier",
     "milestone_description": r"Theorem 5.1 for lattices, with the lattice named: for every norm exponent $p\ge1$ or $p=\infty$, $s=\min\{p,2\}$, every $0<\varepsilon<1/s$, every quadratic verifier $V$ over $\mathbb F_2$ and every choice of tables, the lattice of Lemma 3.12 for the fixed linear system of Construction 4.5 has full rank and dimension $M\le(S+1)^{C}$, and $x\in L(V)$ implies $\operatorname{dist}_p(t_x,\Lambda)\le R$ while $x\notin L(V)$ implies $\operatorname{dist}_p(t_x,\Lambda)>M^{1/s-\varepsilon}\cdot R$, with the radius $R$ of Lemma 3.12." + EXPL},
    {"theorem_name": LP + "ThreeSAT.explicit_code_gap",
     "milestone_title": "Theorem 5.1 (codes, 3SAT) — the paper's code with $M\\le n^{C}$",
     "milestone_description": r"Theorem 5.1 for the nearest codeword problem and the 3SAT verifier, with the code named: for every finite field $F$ and every $0<\varepsilon<1$ there is a constant $C$ such that for every number $v\ge1$ of variables there are tables for which the code of the previous milestone has block length $M\le n^{C}$, $n=(2v)^{3}$, and gap $M^{1-\varepsilon}$ between satisfiable and unsatisfiable instances." + EXPL},
    {"theorem_name": LP + "ThreeSAT.explicit_lattice_gap",
     "milestone_title": "Theorem 5.1 (lattices, 3SAT) — the paper's lattice with $M\\le n^{C}$",
     "milestone_description": r"Theorem 5.1 for the closest vector problem in $\ell_p$ and the 3SAT verifier, with the lattice named: for every $p\ge1$ or $p=\infty$, $s=\min\{p,2\}$, and every $0<\varepsilon<1/s$ there is a constant $C$ such that for every number $v\ge1$ of variables there are tables for which the lattice of the previous milestone has full rank, dimension $M\le n^{C}$, $n=(2v)^{3}$, and gap $M^{1/s-\varepsilon}$ between satisfiable and unsatisfiable instances." + EXPL},
]
json.dump(milestones, open(os.path.join(P, "mission", "milestones_explicit.json"), "w"), indent=1,
          ensure_ascii=False)
print(f"wrote {len(items)} metadata entries and {len(milestones)} milestones")
