import LatticePrepro.ThreeSAT

/-!
# Theorem 5.1 for the paper's construction

The statements of `Main.lean` and `ThreeSAT.lean` assert that *some* fixed code or lattice with
targets has the gap of Theorem 5.1 (`Nonempty (CodeGap …)`, `Nonempty (LatticeGap …)`). The
paper's theorem also requires the code and the map `x ↦ t_x` to be computable in polynomial time.
That requirement is not expressed in Lean, and without it the existence statements say very
little: the target `t_x` is an arbitrary function of the instance, so one can take a code with
two coordinates and let the target record whether `x` is in the language.

This file states Theorem 5.1 for the code and the lattice that the paper constructs, so that
nothing is left to choose except data that does not depend on the instance.

* `QuadraticVerifier.Tables V δ` is that data for a verifier `V` and a gap exponent `δ`: a base
  `B` in the range of the proof of Theorem 4.8 and an explicit moment representation
  (Theorem A.8) with `momentAxes δ` axes and representation bound `B ^ momentAxes δ`.
* `Tables.system` is the fixed linear system `A v = b_x` of Construction 4.5 for these tables.
  The instance enters only through the right-hand side `b_x`, whose nonzero entries are the
  powers `θ_x^k` of the instance encoding.
* `Tables.codeFamily` is the code `ker A × {0}` with the targets of Lemma 3.11, extended to a
  field `F`, and `Tables.latticeFamily`, `Tables.latticeRadius` are the lattice, targets and
  radius of Lemma 3.12 (`LinearSystemFamily.latticeFamily`, `LinearSystemFamily.latticeRadius`).
* `CodeFamily.HasGap` and `LatticeFamily.HasGap` are the conclusions of Theorem 5.1 for a given
  family and radius.

The main statements are `Tables.codeFamily_hasGap` and `Tables.latticeFamily_hasGap` (the gap
holds for every choice of tables), `Tables.nonempty` (tables exist), and their instantiation
with the 3SAT verifier, `ThreeSAT.explicit_code_and_lattice_gaps`.

The targets are still not shown to be computable in polynomial time: `LinearSystemFamily.codeTarget`
picks a solution of `A v = b_x` by classical choice, where the paper uses Gaussian elimination.
The distance from the target to the code does not depend on which solution is picked.
-/

namespace LatticePrepro

/-! ### The conclusion of Theorem 5.1 for a given code or lattice -/

/-- The conclusion of Theorem 5.1 for a given code family `𝒞` and radius `R`: the block length
`M` satisfies `1 ≤ M ≤ n^C`, the radius is at least `1`, instances in `Lang` have
`dist(t_x, 𝒞) ≤ R`, and all other instances have `dist(t_x, 𝒞) > M^{1 - ε} · R`. -/
structure CodeFamily.HasGap {F : Type} [Field F] [DecidableEq F] {X : Type} (𝒞 : CodeFamily F X)
    (R : ℕ) (ε : ℝ) (Lang : Set X) (n C : ℕ) : Prop where
  one_le_R : 1 ≤ R
  one_le_card : 1 ≤ Fintype.card 𝒞.M
  card_le : Fintype.card 𝒞.M ≤ n ^ C
  yes : ∀ x ∈ Lang, CodeFamily.codeDist (𝒞.target x) 𝒞.code ≤ R
  no : ∀ x ∉ Lang,
    (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) * R < CodeFamily.codeDist (𝒞.target x) 𝒞.code

/-- The conclusion of Theorem 5.1 for a given lattice family `Λ`, norm exponent `pn` and radius
`R`: the dimension `M` satisfies `1 ≤ M ≤ n^C`, the radius is at least `1`, the lattice contains
`N · ℤ^M` for some `N > 0` (full rank), instances in `Lang` have `dist_p(t_x, Λ) ≤ R`, and all
other instances have `dist_p(t_x, Λ) > M^{1/s - ε} · R`. -/
structure LatticeFamily.HasGap {X : Type} (Λ : LatticeFamily X) (pn : PNorm) (R : ℕ) (ε : ℝ)
    (Lang : Set X) (n C : ℕ) : Prop where
  one_le_R : 1 ≤ R
  one_le_card : 1 ≤ Fintype.card Λ.M
  card_le : Fintype.card Λ.M ≤ n ^ C
  full_rank : ∃ N : ℕ, 0 < N ∧ ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice
  yes : ∀ x ∈ Lang, Λ.latticeDist pn x ≤ R
  no : ∀ x ∉ Lang, (Fintype.card Λ.M : ℝ) ^ (1 / pn.s - ε) * R < Λ.latticeDist pn x

/-- The same code, with the targets read along a map of instances. -/
def CodeFamily.comap {F : Type} [Field F] {X Y : Type} (𝒞 : CodeFamily F X) (f : Y → X) :
    CodeFamily F Y where
  M := 𝒞.M
  code := 𝒞.code
  target := fun y => 𝒞.target (f y)

/-- The same lattice, with the targets read along a map of instances. -/
def LatticeFamily.comap {X Y : Type} (Λ : LatticeFamily X) (f : Y → X) : LatticeFamily Y where
  M := Λ.M
  lattice := Λ.lattice
  target := fun y => Λ.target (f y)

/-- A gap is transported along a map of instances that respects the languages. -/
theorem CodeFamily.HasGap.comap {F : Type} [Field F] [DecidableEq F] {X Y : Type}
    {𝒞 : CodeFamily F X} {R : ℕ} {ε : ℝ} {Lang : Set X} {n C : ℕ} (h : 𝒞.HasGap R ε Lang n C)
    {Lang' : Set Y} (f : Y → X) (hf : ∀ y, f y ∈ Lang ↔ y ∈ Lang') {n' C' : ℕ}
    (hn : n ^ C ≤ n' ^ C') : (𝒞.comap f).HasGap R ε Lang' n' C' :=
  ⟨h.one_le_R, h.one_le_card, h.card_le.trans hn, fun y hy => h.yes (f y) ((hf y).mpr hy),
    fun y hy => h.no (f y) fun hx => hy ((hf y).mp hx)⟩

/-- A gap is transported along a map of instances that respects the languages. -/
theorem LatticeFamily.HasGap.comap {X Y : Type} {Λ : LatticeFamily X} {pn : PNorm} {R : ℕ}
    {ε : ℝ} {Lang : Set X} {n C : ℕ} (h : Λ.HasGap pn R ε Lang n C) {Lang' : Set Y} (f : Y → X)
    (hf : ∀ y, f y ∈ Lang ↔ y ∈ Lang') {n' C' : ℕ} (hn : n ^ C ≤ n' ^ C') :
    (Λ.comap f).HasGap pn R ε Lang' n' C' :=
  ⟨h.one_le_R, h.one_le_card, h.card_le.trans hn, h.full_rank,
    fun y hy => h.yes (f y) ((hf y).mpr hy), fun y hy => h.no (f y) fun hx => hy ((hf y).mp hx)⟩

/-- A code family with a gap gives the bundled output `CodeGap` of Theorem 5.1. -/
def CodeFamily.HasGap.toCodeGap {F : Type} [Field F] [DecidableEq F] {X : Type}
    {𝒞 : CodeFamily F X} {R : ℕ} {ε : ℝ} {Lang : Set X} {n C : ℕ} (h : 𝒞.HasGap R ε Lang n C) :
    CodeGap F ε Lang n C :=
  ⟨𝒞, R, h.one_le_R, h.one_le_card, h.card_le, h.yes, h.no⟩

/-- A lattice family with a gap gives the bundled output `LatticeGap` of Theorem 5.1. -/
noncomputable def LatticeFamily.HasGap.toLatticeGap {X : Type} {Λ : LatticeFamily X} {pn : PNorm}
    {R : ℕ} {ε : ℝ} {Lang : Set X} {n C : ℕ} (h : Λ.HasGap pn R ε Lang n C) :
    LatticeGap pn ε Lang n C :=
  ⟨Λ, R, h.one_le_R, h.one_le_card, h.card_le, h.full_rank.choose, h.full_rank.choose_spec.1,
    h.full_rank.choose_spec.2, h.yes, h.no⟩

/-! ### The code of Lemma 3.11, and the lattice and the radius of Lemma 3.12 -/

namespace LinearSystemFamily

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

/-- The code family of Lemma 3.11 over a field `F` of characteristic `p`: the code `ker A × {0}`
of the linear system, with the target `(v_x, 0)` for a solution `v_x` of `A v = b_x` if there is
one and `(0, 1)` otherwise, extended to `F`. -/
noncomputable def codeFamily (F : Type) [Field F] [Algebra (ZMod p) F] : CodeFamily F X :=
  CodeFamily.extend F L.toCodeFamily

/-- The block length of the code family is twice the number of columns of the system. -/
lemma card_codeFamily (F : Type) [Field F] [Algebra (ZMod p) F] :
    Fintype.card (L.codeFamily F).M = 2 * Fintype.card L.ι := by
  show Fintype.card (L.ι ⊕ L.ι) = _
  rw [Fintype.card_sum]
  ring

/-- Extension of scalars does not change the distance from the target to the code. -/
lemma codeDist_codeFamily (F : Type) [Field F] [DecidableEq F] [Algebra (ZMod p) F] (x : X) :
    CodeFamily.codeDist ((L.codeFamily F).target x) (L.codeFamily F).code =
      CodeFamily.codeDist (L.codeTarget x) L.code :=
  CodeFamily.codeDist_extend F L.toCodeFamily x

/-- The lattice family of Lemma 3.12 for the norm exponent `pn`: Construction A on the padded
code for `p ≤ 2`, and its blockwise Walsh–Hadamard transform for `p > 2` and `p = ∞`. -/
noncomputable def latticeFamily : PNorm → LatticeFamily X
  | .fin q _ => if q ≤ 2 then L.latticeA else L.latticeH
  | .inf => L.latticeH

/-- The radius of Lemma 3.12 for the norm exponent `pn`, with `D` blocks and padded block size
`2^k`: `⌈D^{1/p}⌉` for `p ≤ 2`, `⌈(2^k · D)^{1/p}⌉` for `2 < p < ∞`, and `1` for `p = ∞`. -/
noncomputable def latticeRadius : PNorm → ℕ
  | .fin q _ =>
      if q ≤ 2 then ⌈(L.numBlocks : ℝ) ^ (1 / q)⌉₊
      else ⌈((2 ^ L.padK : ℝ) * L.numBlocks) ^ (1 / q)⌉₊
  | .inf => 1

/-- **Lemma 3.12** for the lattice of the paper: the lattice reduction of
`exists_latticeReduction` is realized by `latticeFamily` with the radius `latticeRadius`. -/
theorem exists_latticeReduction_eq {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    (pn : PNorm) :
    ∃ Red : LatticeReduction L g pn, Red.Λ = L.latticeFamily pn ∧ Red.R = L.latticeRadius pn := by
  rcases pn with ⟨q, hq⟩ | _
  · rcases le_or_gt q 2 with hq2 | hq2
    · refine ⟨L.reduction_le_two hg hD hq hq2, ?_, ?_⟩
      · show L.latticeA = if q ≤ 2 then L.latticeA else L.latticeH
        rw [if_pos hq2]
      · show ⌈(L.numBlocks : ℝ) ^ (1 / q)⌉₊ = if q ≤ 2 then ⌈(L.numBlocks : ℝ) ^ (1 / q)⌉₊
          else ⌈((2 ^ L.padK : ℝ) * L.numBlocks) ^ (1 / q)⌉₊
        rw [if_pos hq2]
    · refine ⟨L.reduction_gt_two hg hD hq hq2, ?_, ?_⟩
      · show L.latticeH = if q ≤ 2 then L.latticeA else L.latticeH
        rw [if_neg (not_le.mpr hq2)]
      · show ⌈((2 ^ L.padK : ℝ) * L.numBlocks) ^ (1 / q)⌉₊ =
          if q ≤ 2 then ⌈(L.numBlocks : ℝ) ^ (1 / q)⌉₊
          else ⌈((2 ^ L.padK : ℝ) * L.numBlocks) ^ (1 / q)⌉₊
        rw [if_neg (not_le.mpr hq2)]
  · exact ⟨L.reduction_inf hg hD, rfl, rfl⟩

end LinearSystemFamily

/-! ### The tables, and the code and lattice built from them -/

namespace QuadraticVerifier

variable {p : ℕ} [hp : Fact p.Prime]

/-- The data of the construction of Theorem 5.1 that does not depend on the instance, for a
verifier `V` with `S` assignment coordinates and `N` evaluation tables, and a gap exponent `δ`.
With `m = momentAxes δ` and the gap `g = (S + 1)^{gapExp p δ}`, it consists of a base `B ≥ 2`
with `8 N g ≤ B^m ≤ 2^m · 8 N g` (the choice in the proof of Theorem 4.8) and an explicit moment
representation with `m` axes and representation bound `B^m` (Theorem A.8). -/
structure Tables (V : QuadraticVerifier p) (δ : ℝ) where
  /-- The base. -/
  B : ℕ
  two_le_B : 2 ≤ B
  le_pow : 8 * Fintype.card V.TblIdx * (V.S + 1) ^ gapExp p δ ≤ B ^ momentAxes δ
  pow_le : B ^ momentAxes δ ≤
    2 ^ momentAxes δ * (8 * Fintype.card V.TblIdx * (V.S + 1) ^ gapExp p δ)
  /-- The explicit moment representation. -/
  E : ExplicitMomentRepresentation p V.S (momentAxes δ) B

namespace Tables

variable {V : QuadraticVerifier p} {δ : ℝ}

/-- The fixed linear system `A v = b_x` of Construction 4.5 for the tables `T`. The map `A` does
not depend on the instance `x`, and the right-hand side `b_x` is zero except for the powers
`θ_x^k` of the instance encoding in the translation equations. -/
noncomputable def system (T : V.Tables δ) : LinearSystemFamily (ZMod p) (Fin V.n → Bool) :=
  fixedSystem V T.E.R T.E.ε

/-- The code family of Theorem 5.1 for the tables `T` over a field `F` of characteristic `p`:
the code and the targets of Lemma 3.11 for the fixed linear system, extended to `F`. -/
noncomputable def codeFamily (T : V.Tables δ) (F : Type) [Field F] [Algebra (ZMod p) F] :
    CodeFamily F (Fin V.n → Bool) :=
  T.system.codeFamily F

/-- The lattice family of Theorem 5.1 for the tables `T` and the norm exponent `pn`: the lattice
and the targets of Lemma 3.12 for the fixed linear system. -/
noncomputable def latticeFamily (T : V.Tables δ) (pn : PNorm) : LatticeFamily (Fin V.n → Bool) :=
  T.system.latticeFamily pn

/-- The radius of Theorem 5.1 for lattices: the radius of Lemma 3.12 for the fixed linear
system. -/
noncomputable def latticeRadius (T : V.Tables δ) (pn : PNorm) : ℕ := T.system.latticeRadius pn

/-- Tables exist for every verifier with at least two assignment coordinates (the choice of the
base in the proof of Theorem 4.8, and Theorem A.8). -/
theorem nonempty (V : QuadraticVerifier p) (hS : 2 ≤ V.S) {δ : ℝ} (hδ1 : δ < 1) :
    Nonempty (V.Tables δ) := by
  have hm := (momentAxes_spec hδ1).1
  have hN1 : 1 ≤ Fintype.card V.TblIdx := Fintype.card_pos_iff.mpr ⟨Sum.inl V.mainIdx⟩
  have hg : 1 ≤ (V.S + 1) ^ gapExp p δ := Nat.one_le_pow _ _ (by omega)
  obtain ⟨B, hB2, hYB, hBY⟩ :=
    exists_base (Y := 8 * Fintype.card V.TblIdx * (V.S + 1) ^ gapExp p δ) hm
      (Nat.mul_pos (Nat.mul_pos (by norm_num) hN1) hg)
  obtain ⟨E⟩ := exists_explicit_momentRepresentation p V.S (momentAxes δ) B hS hm hB2
  exact ⟨⟨B, hB2, hYB, hBY, E⟩⟩

/-- **Theorem 4.8** for the fixed linear system of the tables `T`, with `m = momentAxes δ` and
the gap `g = (S + 1)^{gapExp p δ}`: the system is a gap reduction from `L(V)` with gap `g`, the
gap is smaller than the block size, there is at least one block, and the number `n` of columns
satisfies `n^m ≤ (8 p^4 m (S + 1))^{(m+7) m} · g^{m+1}`. -/
theorem system_spec (T : V.Tables δ) (hδ1 : δ < 1) :
    T.system.IsGapReduction V.Language ((V.S + 1) ^ gapExp p δ) ∧
      (V.S + 1) ^ gapExp p δ < T.system.blockSize ∧ 0 < T.system.numBlocks ∧
      Fintype.card T.system.ι ^ momentAxes δ ≤
        (8 * p ^ 4 * momentAxes δ * (V.S + 1)) ^ ((momentAxes δ + 7) * momentAxes δ) *
          ((V.S + 1) ^ gapExp p δ) ^ (momentAxes δ + 1) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  have hm := (momentAxes_spec hδ1).1
  set m := momentAxes δ with hmdef
  set g := (V.S + 1) ^ gapExp p δ with hgdef
  set N := Fintype.card V.TblIdx with hNdef
  have hg : 1 ≤ g := Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ N := Fintype.card_pos_iff.mpr ⟨Sum.inl V.mainIdx⟩
  have hNle : N ≤ (V.S + 1) ^ 2 := V.card_tblIdx_le
  have hYB : 8 * N * g ≤ T.B ^ m := T.le_pow
  have hBY : T.B ^ m ≤ 2 ^ m * (8 * N * g) := T.pow_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- gap reduction: `2 g N < r = B^m`
    show (fixedSystem V T.E.R T.E.ε).IsGapReduction V.Language g
    apply FixedSystem.isGapReduction
    rw [T.E.r_eq]
    calc 2 * g * N < 8 * N * g := by nlinarith
      _ ≤ T.B ^ m := hYB
  · -- `g < b = q^m`
    show g < T.E.R.blockSize
    rw [T.E.blockSize_eq]
    calc g < 8 * N * g := by nlinarith
      _ ≤ T.B ^ m := hYB
      _ ≤ T.E.q ^ m := Nat.pow_le_pow_left T.E.le_q m
  · -- the number of blocks `N · D` is positive
    show 0 < (fixedSystem V T.E.R T.E.ε).numBlocks
    rw [FixedSystem.numBlocks_eq]
    exact Nat.mul_pos hN1 T.E.R.numBlocks_pos
  · -- the size bound
    have hcard : Fintype.card (FixedSystem.Col V T.E.R) = N * T.E.q ^ (m + 1) := by
      rw [Fintype.card_prod, T.E.R.card_ι, T.E.numBlocks_eq, T.E.blockSize_eq]; ring
    show Fintype.card (FixedSystem.Col V T.E.R) ^ m ≤ _
    rw [hcard]
    refine size_bound_aux (B := T.B) hp2 hm hS1 hNle ?_ ?_
    · calc T.E.q ≤ 8 * p ^ 3 * m * V.S * T.B := T.E.q_lt.le
        _ ≤ 8 * p ^ 3 * m * (V.S + 1) * T.B := by gcongr; omega
    · calc T.B ^ m ≤ 2 ^ m * (8 * N * g) := hBY
        _ ≤ p ^ m * (8 * N * g) := by gcongr

/-- **Theorem 5.1 for codes**, for the code of the paper: for every finite field `F` of
characteristic `p`, every `0 < ε < 1`, every quadratic verifier `V` over `𝔽_p` and every choice
of tables `T`, the code family `T.codeFamily F` has block length `M ≤ (S + 1)^C` with
`C = sizeExp p (1 - ε)`, and with the radius `R` equal to the number of blocks of the fixed
linear system, `x ∈ L(V)` implies `dist(t_x, 𝒞) ≤ R` and `x ∉ L(V)` implies
`dist(t_x, 𝒞) > M^{1 - ε} · R`. -/
theorem codeFamily_hasGap (F : Type) [Field F] [DecidableEq F] [Algebra (ZMod p) F] {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (T : V.Tables (1 - ε)) :
    (T.codeFamily F).HasGap T.system.numBlocks ε V.Language (V.S + 1) (sizeExp p (1 - ε)) := by
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  obtain ⟨hL, hgb, hDpos, hsize⟩ := T.system_spec (by linarith : 1 - ε < 1)
  have hn1 : 1 ≤ Fintype.card T.system.ι := by
    rw [T.system.card_ι]
    exact Nat.mul_pos hDpos (by omega)
  obtain ⟨h64, hC⟩ := params_spec p (δ := 1 - ε) (by linarith) (by linarith) V.S
    (Fintype.card T.system.ι) hS1 hn1 hsize
  have hM : Fintype.card (T.codeFamily F).M = 2 * Fintype.card T.system.ι :=
    T.system.card_codeFamily F
  have hdist : ∀ x, CodeFamily.codeDist ((T.codeFamily F).target x) (T.codeFamily F).code =
      CodeFamily.codeDist (T.system.codeTarget x) T.system.code :=
    T.system.codeDist_codeFamily F
  have hM4 : Fintype.card (T.codeFamily F).M ≤ 4 * Fintype.card T.system.ι := by omega
  have hMδ : 16 * (Fintype.card (T.codeFamily F).M : ℝ) ^ (1 - ε) ≤
      (((V.S + 1) ^ gapExp p (1 - ε) : ℕ) : ℝ) :=
    rpow_le_of_le_four_mul (by linarith) (by linarith) hM4 h64
  have hDR : (0 : ℝ) < T.system.numBlocks := by exact_mod_cast hDpos
  refine ⟨hDpos, by omega, by omega, ?_, ?_⟩
  · intro x hx
    rw [hdist]
    exact T.system.codeDist_le_of_yes (hL.1 x hx)
  · intro x hx
    rw [hdist]
    have hlt : (V.S + 1) ^ gapExp p (1 - ε) * T.system.numBlocks <
        CodeFamily.codeDist (T.system.codeTarget x) T.system.code :=
      T.system.lt_codeDist_of_no hgb hDpos (hL.2 x hx)
    calc (Fintype.card (T.codeFamily F).M : ℝ) ^ (1 - ε) * (T.system.numBlocks : ℝ)
        ≤ (((V.S + 1) ^ gapExp p (1 - ε) : ℕ) : ℝ) * T.system.numBlocks := by
          gcongr
          linarith [Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card (T.codeFamily F).M)) (1 - ε)]
      _ < CodeFamily.codeDist (T.system.codeTarget x) T.system.code := by exact_mod_cast hlt

/-- Theorem 5.1 for the lattice of the paper, with the gap exponent `δ = 1 - s ε` as a
variable. -/
theorem latticeFamily_hasGap_of_eq (pn : PNorm) {ε δ : ℝ} (hδ : δ = 1 - pn.s * ε) (hε : 0 < ε)
    (hε1 : ε < 1 / pn.s) {V : QuadraticVerifier 2} (T : V.Tables δ) :
    (T.latticeFamily pn).HasGap pn (T.latticeRadius pn) ε V.Language (V.S + 1) (sizeExp 2 δ) := by
  have hs1 := pn.one_le_s
  have hs2 := pn.s_le_two
  have hs0 : 0 < pn.s := by linarith
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    have := (lt_div_iff₀ hs0).mp hε1
    linarith
  have hδ1 : δ < 1 := by rw [hδ]; nlinarith
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  obtain ⟨hL, hgb, hDpos, hsize⟩ := T.system_spec hδ1
  obtain ⟨Red, hΛ, hR⟩ := T.system.exists_latticeReduction_eq hgb hDpos pn
  show (T.system.latticeFamily pn).HasGap pn (T.system.latticeRadius pn) ε V.Language (V.S + 1)
    (sizeExp 2 δ)
  rw [← hΛ, ← hR]
  have hn1 : 1 ≤ Fintype.card T.system.ι := by
    rw [T.system.card_ι]
    exact Nat.mul_pos hDpos (by omega)
  obtain ⟨h64, hC⟩ := params_spec 2 hδ0 hδ1 V.S (Fintype.card T.system.ι) hS1 hn1 hsize
  have hM4 : Fintype.card Red.Λ.M ≤ 4 * Fintype.card T.system.ι := Red.card_lt_four_mul.le
  have h2n : 2 * Fintype.card T.system.ι ≤ Fintype.card Red.Λ.M := Red.two_mul_card_le
  have hMδ : 16 * (Fintype.card Red.Λ.M : ℝ) ^ δ ≤ (((V.S + 1) ^ gapExp 2 δ : ℕ) : ℝ) :=
    rpow_le_of_le_four_mul hδ0 hδ1.le hM4 h64
  have hexp : δ * (pn.s)⁻¹ = 1 / pn.s - ε := by rw [hδ]; field_simp
  have hRR : (0 : ℝ) < Red.R := by exact_mod_cast Red.one_le_R
  have hDR : (0 : ℝ) < T.system.numBlocks := by exact_mod_cast hDpos
  -- NO instances: every lattice vector is far from the target
  have hno : ∀ x ∉ V.Language, ∀ v ∈ Red.Λ.lattice,
      (Fintype.card Red.Λ.M : ℝ) ^ (1 / pn.s - ε) * Red.R < Red.Λ.dist pn x v := by
    intro x hx v hv
    have hgw : (((V.S + 1) ^ gapExp 2 δ : ℕ) : ℝ) * T.system.numBlocks < Red.weight x v := by
      exact_mod_cast Red.lt_weight x (hL.2 x hx) v hv
    have hdist0 : 0 ≤ Red.Λ.dist pn x v := pn.norm_nonneg _
    -- `g D < w ≤ 16 D (dist/R)^s`, hence `g / 16 < (dist/R)^s`
    have h1 : (((V.S + 1) ^ gapExp 2 δ : ℕ) : ℝ) < 16 * (Red.Λ.dist pn x v / Red.R) ^ pn.s := by
      have : (((V.S + 1) ^ gapExp 2 δ : ℕ) : ℝ) * T.system.numBlocks <
          16 * (Red.Λ.dist pn x v / Red.R) ^ pn.s * T.system.numBlocks := by
        calc (((V.S + 1) ^ gapExp 2 δ : ℕ) : ℝ) * T.system.numBlocks < Red.weight x v := hgw
          _ ≤ 16 * T.system.numBlocks * (Red.Λ.dist pn x v / Red.R) ^ pn.s :=
              Red.weight_le x v hv
          _ = 16 * (Red.Λ.dist pn x v / Red.R) ^ pn.s * T.system.numBlocks := by ring
      exact lt_of_mul_lt_mul_right this hDR.le
    have h2 : (Fintype.card Red.Λ.M : ℝ) ^ δ < (Red.Λ.dist pn x v / Red.R) ^ pn.s := by linarith
    -- take `(1/s)`-th powers
    have h3 : ((Fintype.card Red.Λ.M : ℝ) ^ δ) ^ (pn.s)⁻¹ <
        ((Red.Λ.dist pn x v / Red.R) ^ pn.s) ^ (pn.s)⁻¹ :=
      Real.rpow_lt_rpow (by positivity) h2 (by positivity)
    rw [Real.rpow_rpow_inv (by positivity) hs0.ne', ← Real.rpow_mul (by positivity)] at h3
    rw [hexp, lt_div_iff₀ hRR] at h3
    exact h3
  exact ⟨Red.one_le_R, by omega, by omega, ⟨Red.N, Red.N_pos, Red.smul_mem⟩,
    fun x hx => Red.Λ.latticeDist_le_of_exists pn x (Red.yes x (hL.1 x hx)),
    fun x hx => Red.Λ.lt_latticeDist_of_forall pn x (hno x hx)⟩

/-- **Theorem 5.1 for lattices**, for the lattice of the paper: for every norm exponent
`1 ≤ p ≤ ∞` with `s = min {p, 2}`, every `0 < ε < 1/s`, every quadratic verifier `V` over `𝔽_2`
and every choice of tables `T`, the lattice family `T.latticeFamily pn` has full rank and
dimension `M ≤ (S + 1)^C` with `C = sizeExp 2 (1 - s ε)`, and with the radius
`R = T.latticeRadius pn`, `x ∈ L(V)` implies `dist_p(t_x, Λ) ≤ R` and `x ∉ L(V)` implies
`dist_p(t_x, Λ) > M^{1/s - ε} · R`. -/
theorem latticeFamily_hasGap (pn : PNorm) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / pn.s)
    {V : QuadraticVerifier 2} (T : V.Tables (1 - pn.s * ε)) :
    (T.latticeFamily pn).HasGap pn (T.latticeRadius pn) ε V.Language (V.S + 1)
      (sizeExp 2 (1 - pn.s * ε)) :=
  latticeFamily_hasGap_of_eq pn rfl hε hε1 T

end Tables

end QuadraticVerifier

/-! ### Theorem 5.1 for 3SAT, for the paper's construction -/

namespace ThreeSAT

open QuadraticVerifier

/-- The 3SAT verifier has at least two assignment coordinates. -/
lemma two_le_S_verifier (p : ℕ) {v : ℕ} (hv : 1 ≤ v) : 2 ≤ (verifier p v).S := by
  have h1 := S_verifier_succ_le p hv
  have h2 := (verifier p v).n_succ_le
  have h3 : (verifier p v).n = len v := rfl
  have h8 := eight_le_len hv
  omega

/-- **Theorem 5.1 for 3SAT, codes, for the paper's construction**: for every finite field `F` of
characteristic `p` and every `0 < ε < 1`, there is a constant `C` such that for every `v ≥ 1`
there are tables `T` for the 3SAT verifier on `v` variables for which the code family
`T.codeFamily F`, with the instances encoded by `encode`, has block length `M ≤ n^C`
(`n = (2v)^3` the instance length) and gap `M^{1 - ε}` for 3SAT, with the radius equal to the
number of blocks of the fixed linear system. -/
theorem explicit_code_gap (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier p v).Tables (1 - ε),
      ((T.codeFamily F).comap encode).HasGap T.system.numBlocks ε (SAT v) (len v) C := by
  refine ⟨3 * sizeExp p (1 - ε), fun v hv => ?_⟩
  obtain ⟨T⟩ := Tables.nonempty (verifier p v) (two_le_S_verifier p hv)
    (by linarith : 1 - ε < 1)
  refine ⟨T, (T.codeFamily_hasGap F hε hε1).comap encode
    (fun x => mem_language_verifier_iff p x) ?_⟩
  rw [pow_mul]
  exact Nat.pow_le_pow_left (S_verifier_succ_le p hv) _

/-- **Theorem 5.1 for 3SAT, lattices, for the paper's construction**: for every norm exponent
`1 ≤ p ≤ ∞` with `s = min {p, 2}` and every `0 < ε < 1/s`, there is a constant `C` such that for
every `v ≥ 1` there are tables `T` for the 3SAT verifier on `v` variables for which the lattice
family `T.latticeFamily pn`, with the instances encoded by `encode`, has full rank, dimension
`M ≤ n^C` (`n = (2v)^3` the instance length) and gap `M^{1/s - ε}` for 3SAT, with the radius
`T.latticeRadius pn`. -/
theorem explicit_lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier 2 v).Tables (1 - pn.s * ε),
      ((T.latticeFamily pn).comap encode).HasGap pn (T.latticeRadius pn) ε (SAT v) (len v) C := by
  have hδ1 : 1 - pn.s * ε < 1 := by nlinarith [pn.one_le_s]
  refine ⟨3 * sizeExp 2 (1 - pn.s * ε), fun v hv => ?_⟩
  obtain ⟨T⟩ := Tables.nonempty (verifier 2 v) (two_le_S_verifier 2 hv) hδ1
  refine ⟨T, (T.latticeFamily_hasGap pn hε hε1).comap encode
    (fun x => mem_language_verifier_iff 2 x) ?_⟩
  rw [pow_mul]
  exact Nat.pow_le_pow_left (S_verifier_succ_le 2 hv) _

/-- **Theorem 5.1** (fixed code and lattice gaps) for 3SAT, for the code and the lattice that the
paper constructs. The code is `ker A × {0}` for the fixed linear system `A v = b_x` of
Construction 4.5 (extended to `F`), with the targets of Lemma 3.11, and the lattice and its
targets are those of Lemma 3.12 for the same system. Only the tables `T`, which do not depend on
the instance, are asserted to exist; the instance enters through the right-hand side `b_x`
alone. For every finite field `F` and every `0 < ε < 1` this code has gap `M^{1 - ε}`, and for
every norm exponent `1 ≤ p ≤ ∞` and every `0 < ε < 1/s`, `s = min {p, 2}`, this lattice has gap
`M^{1/s - ε}`; in both cases `M ≤ n^C` in the instance length `n`.

Unlike `fixed_code_and_lattice_gaps`, this statement cannot be met by a code or lattice whose
targets are chosen according to whether the instance is satisfiable. -/
theorem explicit_code_and_lattice_gaps :
    (∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [DecidableEq F]
        [Algebra (ZMod p) F] (ε : ℝ), 0 < ε → ε < 1 →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier p v).Tables (1 - ε),
          ((T.codeFamily F).comap encode).HasGap T.system.numBlocks ε (SAT v) (len v) C) ∧
      (∀ (pn : PNorm) (ε : ℝ), 0 < ε → ε < 1 / pn.s →
        ∃ C : ℕ, ∀ v : ℕ, 1 ≤ v → ∃ T : (verifier 2 v).Tables (1 - pn.s * ε),
          ((T.latticeFamily pn).comap encode).HasGap pn (T.latticeRadius pn) ε (SAT v) (len v)
            C) :=
  ⟨fun p _ F _ _ _ _ ε hε hε1 => explicit_code_gap p F ε hε hε1, explicit_lattice_gap⟩

end ThreeSAT

end LatticePrepro
