import LatticePrepro.Basic.Nat
import LatticePrepro.Reduction.Soundness
import LatticePrepro.Tables.Explicit
import LatticePrepro.Conversions.Codes
import LatticePrepro.Conversions.Lattices
import LatticePrepro.Conversions.SearchTest
import LatticePrepro.Lattices.Distance
import LatticePrepro.Lattices.Mathlib

/-!
# Main results

* **Theorem 4.7** (`GapReduction`, `exists_gapReduction`): for every prime `p`, quadratic
  verifier `V` with `S` coordinates, gap `g ≥ 1` and `m ≥ 1`, there is a linear system family
  over `𝔽_p` that is a gap reduction from the language of `V` with gap `g`, with `g < b` and
  `n^m ≤ (8 p^4 m (S+1))^{(m+7) m} · g^{m+1}` columns.
* **Theorem 5.1** (`CodeGap`, `LatticeGap`, `code_gap`, `lattice_gap`, `exists_code_gap`,
  `exists_lattice_gap`): fixed codes over any finite field, and fixed lattices in any `ℓ_p`
  norm, with polynomial dimension `M ≤ (S + 1)^C` and approximation gap `M^{1/s - ε}` measured
  by `dist(t_x, 𝒞)` and `dist_p(t_x, Λ)`, together with the search test of Lemma 5.2. The
  exponent `C = sizeExp p δ` is explicit (`δ = 1 - s ε`).

The polynomial-time computability claims of the paper are not formalized.
-/

namespace LatticePrepro

/-! ### Restricting an encoding tuple to fewer coordinates -/

/-- The first `S + 1` entries of an encoding tuple of length `S' ≥ S`. -/
def EncodingTuple.castLE {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {S S' : ℕ} (h : S ≤ S') (ε : EncodingTuple p K S') : EncodingTuple p K S where
  E := fun i => ε.E (Fin.castLE (by omega) i)
  E_zero := by simpa using ε.E_zero
  linearIndependent := by
    have := ε.linearIndependent.comp (Fin.castLE h) (Fin.castLE_injective h)
    convert this using 1
    funext i
    simp only [Function.comp]
    rfl

/-! ### Theorem 4.7 -/

/-- Exponent bookkeeping for the size bound of Theorem 4.7. -/
lemma size_bound_aux {p m S N q B g : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) (hS : 1 ≤ S)
    (hN : N ≤ (S + 1) ^ 2) (hq : q ≤ 8 * p ^ 3 * m * (S + 1) * B)
    (hB : B ^ m ≤ p ^ m * (8 * N * g)) :
    (N * q ^ (m + 1)) ^ m ≤ (8 * p ^ 4 * m * (S + 1)) ^ ((m + 7) * m) * g ^ (m + 1) := by
  set X := 8 * p ^ 3 * m * (S + 1) with hX
  have h8pm : 1 ≤ 8 * p ^ 3 * m :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega))) hm
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hSX : S + 1 ≤ X := by rw [hX]; nlinarith
  have hNX : N ≤ X ^ 2 := hN.trans (Nat.pow_le_pow_left hSX 2)
  have h8 : 8 ^ (m + 1) ≤ p ^ (6 * m) := by
    calc 8 ^ (m + 1) = 8 * 8 ^ m := by ring
      _ ≤ 8 ^ m * 8 ^ m := by
          apply Nat.mul_le_mul_right
          calc 8 = 8 ^ 1 := by norm_num
            _ ≤ 8 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      _ = 64 ^ m := by rw [← mul_pow]; norm_num
      _ ≤ (p ^ 6) ^ m := by
          apply Nat.pow_le_pow_left
          calc 64 = 2 ^ 6 := by norm_num
            _ ≤ p ^ 6 := Nat.pow_le_pow_left hp 6
      _ = p ^ (6 * m) := by rw [← pow_mul]
  have hexp : m * m + 5 * m + 2 ≤ m * (m + 7) := by nlinarith
  have hpX : 8 * p ^ 4 * m * (S + 1) = p * X := by rw [hX]; ring
  calc (N * q ^ (m + 1)) ^ m = N ^ m * (q ^ m) ^ (m + 1) := by ring
    _ ≤ N ^ m * ((X * B) ^ m) ^ (m + 1) := by gcongr
    _ = N ^ m * (X ^ m * B ^ m) ^ (m + 1) := by rw [mul_pow]
    _ ≤ N ^ m * (X ^ m * (p ^ m * (8 * N * g))) ^ (m + 1) := by gcongr
    _ = 8 ^ (m + 1) * N ^ (2 * m + 1) * (X ^ (m * (m + 1)) * p ^ (m * (m + 1))) * g ^ (m + 1) := by
        ring
    _ ≤ p ^ (6 * m) * (X ^ 2) ^ (2 * m + 1) * (X ^ (m * (m + 1)) * p ^ (m * (m + 1))) *
          g ^ (m + 1) := by gcongr
    _ = p ^ (m * (m + 7)) * X ^ (m * m + 5 * m + 2) * g ^ (m + 1) := by ring_nf
    _ ≤ p ^ (m * (m + 7)) * X ^ (m * (m + 7)) * g ^ (m + 1) := by
        gcongr
    _ = (8 * p ^ 4 * m * (S + 1)) ^ ((m + 7) * m) * g ^ (m + 1) := by
        rw [hpX]; ring_nf

/-- The output of Theorem 4.7 for a verifier `V`, a gap `g` and `m ≥ 1`: a linear system family
`L` over `𝔽_p` that is a gap reduction from `L(V)` with gap `g < b` (`b` a power of `p`), with at
least one block and `n^m ≤ (8 p^4 m (S + 1))^{(m+7) m} · g^{m+1}` columns. -/
structure GapReduction (p : ℕ) [Fact p.Prime] (V : QuadraticVerifier p) (g m : ℕ) where
  /-- The fixed linear system. -/
  L : LinearSystemFamily (ZMod p) (Fin V.n → Bool)
  isGapReduction : L.IsGapReduction V.Language g
  lt_blockSize : g < L.blockSize
  blockSize_eq_pow : ∃ e : ℕ, L.blockSize = p ^ e
  numBlocks_pos : 0 < L.numBlocks
  card_pow_le : (Fintype.card L.ι) ^ m ≤ (8 * p ^ 4 * m * (V.S + 1)) ^ ((m + 7) * m) * g ^ (m + 1)

/-- **Theorem 4.7** (size and gap), existence form. -/
theorem exists_gapReduction (p : ℕ) [hp : Fact p.Prime] (V : QuadraticVerifier p) (g m : ℕ)
    (hg : 1 ≤ g) (hm : 1 ≤ m) : Nonempty (GapReduction p V g m) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  -- the number of tables
  set N := Fintype.card V.TblIdx with hNdef
  have hN1 : 1 ≤ N := Fintype.card_pos_iff.mpr ⟨Sum.inl V.mainIdx⟩
  have hNle : N ≤ (V.S + 1) ^ 2 := V.card_tblIdx_le
  -- the base `B`
  obtain ⟨B, hB2, hYB, hBY⟩ :=
    exists_base (Y := 8 * N * g) hm (Nat.mul_pos (Nat.mul_pos (by norm_num) hN1) hg)
  -- the explicit moment representation, for `S' = max S 2 ≤ S + 1`
  set S' := max V.S 2 with hS'
  have hSS' : V.S ≤ S' := le_max_left _ _
  have hS'2 : 2 ≤ S' := le_max_right _ _
  have hS'le : S' ≤ V.S + 1 := max_le (by omega) (by omega)
  obtain ⟨E⟩ := exists_explicit_momentRepresentation p S' m B hS'2 hm hB2
  obtain ⟨d, hd, hqd⟩ := E.q_eq_pow
  let ε : EncodingTuple p E.K V.S := E.ε.castLE hSS'
  refine ⟨⟨fixedSystem V E.R ε, ?_, ?_, ⟨d * m, ?_⟩, ?_, ?_⟩⟩
  · -- gap reduction: `2 g N < r = B^m`
    apply FixedSystem.isGapReduction
    rw [E.r_eq]
    calc 2 * g * N < 8 * N * g := by nlinarith
      _ ≤ B ^ m := hYB
  · -- `g < b = q^m`
    show g < E.R.blockSize
    rw [E.blockSize_eq]
    calc g < 8 * N * g := by nlinarith
      _ ≤ B ^ m := hYB
      _ ≤ E.q ^ m := Nat.pow_le_pow_left E.le_q m
  · show E.R.blockSize = p ^ (d * m)
    rw [E.blockSize_eq, hqd, ← pow_mul]
  · -- the number of blocks `N · D` is positive
    rw [FixedSystem.numBlocks_eq]
    exact Nat.mul_pos hN1 E.R.numBlocks_pos
  · -- the size bound
    have hcard : Fintype.card (FixedSystem.Col V E.R) = N * E.q ^ (m + 1) := by
      rw [Fintype.card_prod, E.R.card_ι, E.numBlocks_eq, E.blockSize_eq]; ring
    show Fintype.card (FixedSystem.Col V E.R) ^ m ≤ _
    rw [hcard]
    refine size_bound_aux (B := B) hp2 hm hS1 hNle ?_ ?_
    · calc E.q ≤ 8 * p ^ 3 * m * S' * B := E.q_lt.le
        _ ≤ 8 * p ^ 3 * m * (V.S + 1) * B := by gcongr
    · calc B ^ m ≤ 2 ^ m * (8 * N * g) := hBY
        _ ≤ p ^ m * (8 * N * g) := by gcongr

/-! ### Choice of parameters for Theorem 5.1

For a gap exponent `0 ≤ δ < 1` we choose `m` with `δ (1 + 1/m) < 1`, then the gap `g = (S+1)^k`
with `k` large enough that `64 · n^δ ≤ g`, and the size exponent `C` with `4 n ≤ (S+1)^C`, where
`n^m ≤ (8 p^4 m (S+1))^{(m+7) m} g^{m+1}` is the column bound of Theorem 4.7. All three
constants are explicit functions of `p` and `δ`. -/

/-- The number of moment axes `m = ⌈δ / (1 - δ)⌉ + 1`, so that `δ (m + 1) < m`. -/
noncomputable def momentAxes (δ : ℝ) : ℕ := ⌈δ / (1 - δ)⌉₊ + 1

/-- The exponent `a = (8 p^4 m + 1) (m + 7) m`, with `(8 p^4 m (S+1))^{(m+7) m} ≤ (S+1)^a`. -/
def prefactorExp (p m : ℕ) : ℕ := (8 * p ^ 4 * m + 1) * ((m + 7) * m)

/-- The gap exponent `k`, giving the gap `g = (S+1)^k`. -/
noncomputable def gapExp (p : ℕ) (δ : ℝ) : ℕ :=
  ⌈(6 * momentAxes δ + prefactorExp p (momentAxes δ) : ℝ) /
    (momentAxes δ - δ * (momentAxes δ + 1))⌉₊ + 1

/-- The size exponent `C`, giving `M ≤ (S+1)^C`. -/
noncomputable def sizeExp (p : ℕ) (δ : ℝ) : ℕ :=
  prefactorExp p (momentAxes δ) + gapExp p δ * (momentAxes δ + 1) + 2

lemma momentAxes_spec {δ : ℝ} (hδ1 : δ < 1) :
    1 ≤ momentAxes δ ∧ δ * (momentAxes δ + 1) < momentAxes δ := by
  refine ⟨by unfold momentAxes; omega, ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  have hm : δ / (1 - δ) < momentAxes δ := by
    unfold momentAxes
    push_cast
    linarith [Nat.le_ceil (δ / (1 - δ))]
  rw [div_lt_iff₀ h1δ] at hm
  nlinarith

/-- Parameter choice: given `0 ≤ δ < 1`, with `m = momentAxes δ`, `k = gapExp p δ` and
`C = sizeExp p δ`, for every `S ≥ 1` and `g = (S+1)^k`, any `n ≥ 1` with
`n^m ≤ (8 p^4 m (S+1))^{(m+7) m} g^{m+1}` satisfies `64 · n^δ ≤ g` and `4 n ≤ (S+1)^C`. -/
lemma params_spec (p : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (S n : ℕ) (hS : 1 ≤ S)
    (hn : 1 ≤ n)
    (hbound : n ^ momentAxes δ ≤ (8 * p ^ 4 * momentAxes δ * (S + 1)) ^
      ((momentAxes δ + 7) * momentAxes δ) * ((S + 1) ^ gapExp p δ) ^ (momentAxes δ + 1)) :
    64 * (n : ℝ) ^ δ ≤ ((S + 1) ^ gapExp p δ : ℕ) ∧ 4 * n ≤ (S + 1) ^ sizeExp p δ := by
  obtain ⟨hm1, hmδ⟩ := momentAxes_spec hδ1
  set m := momentAxes δ with hm
  set a : ℕ := prefactorExp p m with ha
  set η : ℝ := m - δ * (m + 1) with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  set k : ℕ := gapExp p δ with hk
  have hkdef : k = ⌈(6 * m + a : ℝ) / η⌉₊ + 1 := rfl
  have hC : sizeExp p δ = a + k * (m + 1) + 2 := rfl
  rw [hC]
  have hS2 : (2 : ℝ) ≤ (S + 1 : ℕ) := by exact_mod_cast (by omega : 2 ≤ S + 1)
  have hS1R : (1 : ℝ) ≤ (S + 1 : ℕ) := by linarith
  have hS0R : (0 : ℝ) < (S + 1 : ℕ) := by linarith
  -- the prefactor is at most `(S+1)^a` (in exponent form)
  have hX : 8 * p ^ 4 * m * (S + 1) ≤ (S + 1) ^ (8 * p ^ 4 * m + 1) := by
    calc 8 * p ^ 4 * m * (S + 1) ≤ 2 ^ (8 * p ^ 4 * m) * (S + 1) := by
          gcongr
          exact (Nat.lt_two_pow_self).le
      _ ≤ (S + 1) ^ (8 * p ^ 4 * m) * (S + 1) := by
          gcongr
          omega
      _ = (S + 1) ^ (8 * p ^ 4 * m + 1) := by ring
  have hn' : n ^ m ≤ (S + 1) ^ (a + k * (m + 1)) := by
    calc n ^ m ≤ (8 * p ^ 4 * m * (S + 1)) ^ ((m + 7) * m) * ((S + 1) ^ k) ^ (m + 1) := hbound
      _ ≤ ((S + 1) ^ (8 * p ^ 4 * m + 1)) ^ ((m + 7) * m) * ((S + 1) ^ k) ^ (m + 1) := by
          gcongr
      _ = (S + 1) ^ (a + k * (m + 1)) := by
          rw [ha, prefactorExp, ← pow_mul, ← pow_mul, ← pow_add]
  constructor
  · -- `64 n^δ ≤ (S+1)^k`, by raising both sides to the `m`-th power
    set T : ℝ := ((S + 1 : ℕ) : ℝ) with hT
    have hT1 : (1 : ℝ) ≤ T := hS1R
    have hT0 : (0 : ℝ) < T := hS0R
    have hT2 : (2 : ℝ) ≤ T := hS2
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn'R : ((n : ℝ) ^ m) ≤ T ^ (a + k * (m + 1)) := by rw [hT]; exact_mod_cast hn'
    have hkη : (6 * m + a : ℝ) ≤ k * η := by
      have h1 : (6 * m + a : ℝ) / η ≤ ⌈(6 * m + a : ℝ) / η⌉₊ := Nat.le_ceil _
      have h2 : (⌈(6 * m + a : ℝ) / η⌉₊ : ℝ) ≤ k := by rw [hkdef]; push_cast; linarith
      calc (6 * m + a : ℝ) = (6 * m + a : ℝ) / η * η := by field_simp
        _ ≤ k * η := by gcongr; linarith
    have hexp : (6 * m : ℝ) + ((a + k * (m + 1) : ℕ) : ℝ) * δ ≤ ((k * m : ℕ) : ℝ) := by
      have : δ * (a : ℝ) ≤ a := by nlinarith
      rw [hη] at hkη
      push_cast
      nlinarith
    have e1 : (64 * (n : ℝ) ^ δ) ^ m = 64 ^ m * ((n : ℝ) ^ m) ^ δ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_natCast_mul (by positivity),
        mul_comm δ (m : ℝ)]
    have e2 : (64 : ℝ) ^ m ≤ T ^ (6 * m) := by
      calc (64 : ℝ) ^ m = (2 ^ 6) ^ m := by norm_num
        _ ≤ (T ^ 6) ^ m := by gcongr
        _ = T ^ (6 * m) := by rw [← pow_mul]
    have key : (64 * (n : ℝ) ^ δ) ^ m ≤ (((S + 1) ^ k : ℕ) : ℝ) ^ m := by
      calc (64 * (n : ℝ) ^ δ) ^ m = 64 ^ m * ((n : ℝ) ^ m) ^ δ := e1
        _ ≤ T ^ (6 * m) * (T ^ (a + k * (m + 1))) ^ δ := by gcongr
        _ = T ^ ((6 * m : ℕ) : ℝ) * T ^ (((a + k * (m + 1) : ℕ) : ℝ) * δ) := by
            rw [Real.rpow_natCast, Real.rpow_natCast_mul hT0.le]
        _ = T ^ (((6 * m : ℕ) : ℝ) + ((a + k * (m + 1) : ℕ) : ℝ) * δ) := by
            rw [Real.rpow_add hT0]
        _ ≤ T ^ (((k * m : ℕ) : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le hT1
            push_cast at hexp ⊢
            exact hexp
        _ = (((S + 1) ^ k : ℕ) : ℝ) ^ m := by
            rw [Real.rpow_natCast, hT]; push_cast; ring_nf
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp key
  · -- `4 n ≤ (S+1)^C`
    have hnn : n ≤ n ^ m := Nat.le_self_pow (by omega) n
    calc 4 * n ≤ (S + 1) ^ 2 * (S + 1) ^ (a + k * (m + 1)) := by
          apply Nat.mul_le_mul
          · calc 4 = 2 ^ 2 := by norm_num
              _ ≤ (S + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          · exact hnn.trans hn'
      _ = (S + 1) ^ (a + k * (m + 1) + 2) := by ring

/-- From the parameter choice: `16 · M^δ ≤ g` whenever `M ≤ 4 n` and `64 n^δ ≤ g`. -/
lemma rpow_le_of_le_four_mul {M n : ℕ} {g δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hM : M ≤ 4 * n)
    (h64 : 64 * (n : ℝ) ^ δ ≤ g) : 16 * (M : ℝ) ^ δ ≤ g := by
  have hMR : (M : ℝ) ≤ 4 * n := by exact_mod_cast hM
  calc 16 * (M : ℝ) ^ δ ≤ 16 * (4 * (n : ℝ)) ^ δ := by gcongr
    _ = 16 * (4 : ℝ) ^ δ * (n : ℝ) ^ δ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    _ ≤ 16 * 4 * (n : ℝ) ^ δ := by
        gcongr
        calc (4 : ℝ) ^ δ ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
          _ = 4 := Real.rpow_one 4
    _ = 64 * (n : ℝ) ^ δ := by ring
    _ ≤ g := h64

/-! ### Theorem 5.1 for codes -/

/-- A fixed code with gap `M^{1 - ε}` for a language `Lang ⊆ X` with size parameter `n` and
exponent `C` (the conclusion of Theorem 5.1 for codes, together with the search test of
Lemma 5.2): a code `𝒞 ⊆ F^M` with `1 ≤ M ≤ n^C`, targets `t_x` and an integer radius `R ≥ 1`
such that `x ∈ Lang` implies `dist(t_x, 𝒞) ≤ R` and `x ∉ Lang` implies
`dist(t_x, 𝒞) > M^{1 - ε} · R`; and a test accepting every `M^{1-ε}`-approximate solution on
`x ∈ Lang` and rejecting every vector on `x ∉ Lang`. -/
structure CodeGap (F : Type) [Field F] [DecidableEq F] (ε : ℝ) {X : Type} (Lang : Set X)
    (n C : ℕ) where
  /-- The fixed code and the targets. -/
  𝒞 : CodeFamily F X
  /-- The radius. -/
  R : ℕ
  one_le_R : 1 ≤ R
  one_le_card : 1 ≤ Fintype.card 𝒞.M
  card_le : Fintype.card 𝒞.M ≤ n ^ C
  yes : ∀ x ∈ Lang, CodeFamily.codeDist (𝒞.target x) 𝒞.code ≤ R
  no : ∀ x ∉ Lang,
    (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) * R < CodeFamily.codeDist (𝒞.target x) 𝒞.code
  /-- The test of Lemma 5.2. -/
  accepts : X → (𝒞.M → F) → Prop
  accepts_of_isApprox : ∀ x ∈ Lang, ∀ c,
    𝒞.IsApprox ((Fintype.card 𝒞.M : ℝ) ^ (1 - ε)) x c → accepts x c
  not_accepts : ∀ x ∉ Lang, ∀ c, ¬ accepts x c

/-- Transport a fixed code gap along a map of instances that respects the languages. -/
def CodeGap.comap {F : Type} [Field F] [DecidableEq F] {ε : ℝ} {X Y : Type} {Lang : Set X}
    {n C : ℕ} (G : CodeGap F ε Lang n C) {Lang' : Set Y} (f : Y → X)
    (hf : ∀ y, f y ∈ Lang ↔ y ∈ Lang') {n' C' : ℕ} (hn : n ^ C ≤ n' ^ C') :
    CodeGap F ε Lang' n' C' where
  𝒞 := { M := G.𝒞.M, code := G.𝒞.code, target := fun y => G.𝒞.target (f y) }
  R := G.R
  one_le_R := G.one_le_R
  one_le_card := G.one_le_card
  card_le := G.card_le.trans hn
  yes := fun y hy => G.yes (f y) ((hf y).mpr hy)
  no := fun y hy => G.no (f y) (fun h => hy ((hf y).mp h))
  accepts := fun y c => G.accepts (f y) c
  accepts_of_isApprox := fun y hy c hc => G.accepts_of_isApprox (f y) ((hf y).mpr hy) c hc
  not_accepts := fun y hy c => G.not_accepts (f y) (fun h => hy ((hf y).mp h)) c

/-- **Theorem 5.1 for codes**, with the explicit exponent `C = sizeExp p (1 - ε)`: for every
finite field `F` of characteristic `p`, every `0 < ε < 1` and every quadratic verifier `V` over
`𝔽_p`, there is a fixed code of block length `M ≤ (S + 1)^C` with gap `M^{1 - ε}` for `L(V)`. -/
theorem code_gap (p : ℕ) [hp : Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (V : QuadraticVerifier p) :
    Nonempty (CodeGap F ε V.Language (V.S + 1) (sizeExp p (1 - ε))) := by
  have hm := (momentAxes_spec (δ := 1 - ε) (by linarith)).1
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  obtain ⟨⟨L, hL, hgb, -, hDpos, hsize⟩⟩ := exists_gapReduction p V
    ((V.S + 1) ^ gapExp p (1 - ε)) (momentAxes (1 - ε)) (Nat.one_le_pow _ _ (by omega)) hm
  set n := Fintype.card L.ι with hn
  have hn1 : 1 ≤ n := by
    rw [hn, L.card_ι]
    exact Nat.mul_pos hDpos (by omega)
  obtain ⟨h64, hC⟩ := params_spec p (δ := 1 - ε) (by linarith) (by linarith) V.S n hS1 hn1 hsize
  set g := (V.S + 1) ^ gapExp p (1 - ε) with hg
  -- the code over `F`
  set 𝒞 := (L.toCodeFamily).extend F with h𝒞
  have hM : Fintype.card 𝒞.M = Fintype.card (L.ι ⊕ L.ι) := rfl
  have hdist : ∀ x, CodeFamily.codeDist (𝒞.target x) 𝒞.code =
      CodeFamily.codeDist (L.codeTarget x) L.code := fun x => CodeFamily.codeDist_extend F _ x
  have hM4 : Fintype.card 𝒞.M ≤ 4 * n := by rw [hM, Fintype.card_sum]; omega
  have hMδ : 16 * (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) ≤ g :=
    rpow_le_of_le_four_mul (by linarith) (by linarith) hM4 h64
  have hDR : (0 : ℝ) < L.numBlocks := by exact_mod_cast hDpos
  have hyes : ∀ x ∈ V.Language, CodeFamily.codeDist (𝒞.target x) 𝒞.code ≤ L.numBlocks := by
    intro x hx
    rw [hdist]
    exact L.codeDist_le_of_yes (hL.1 x hx)
  have hno : ∀ x ∉ V.Language,
      (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) * L.numBlocks <
        CodeFamily.codeDist (𝒞.target x) 𝒞.code := by
    intro x hx
    rw [hdist]
    have hlt : g * L.numBlocks < CodeFamily.codeDist (L.codeTarget x) L.code :=
      L.lt_codeDist_of_no hgb hDpos (hL.2 x hx)
    calc (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) * (L.numBlocks : ℝ)
        ≤ (g : ℝ) * L.numBlocks := by
          gcongr
          linarith [Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card 𝒞.M)) (1 - ε)]
      _ < CodeFamily.codeDist (L.codeTarget x) L.code := by exact_mod_cast hlt
  refine ⟨⟨𝒞, L.numBlocks, hDpos, ?_, ?_, hyes, hno, 𝒞.Accepts g L.numBlocks, ?_, ?_⟩⟩
  · rw [hM, Fintype.card_sum]; omega
  · rw [hM, Fintype.card_sum]; omega
  · intro x hx c hc
    refine 𝒞.accepts_of_isApprox (hyes x hx) ?_ hc
    have := Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card 𝒞.M)) (1 - ε)
    linarith
  · intro x hx c
    refine 𝒞.not_accepts_of_lt ?_ c
    have h1 := hno x hx
    have h2 : (g : ℝ) * L.numBlocks < CodeFamily.codeDist (𝒞.target x) 𝒞.code := by
      rw [hdist]
      exact_mod_cast L.lt_codeDist_of_no hgb hDpos (hL.2 x hx)
    exact_mod_cast h2

/-- **Theorem 5.1 for codes**, paper form: for every finite field `F` of characteristic `p` and
every `0 < ε < 1`, there is a constant `C` such that every quadratic verifier `V` over `𝔽_p`
admits a fixed code of block length `M ≤ (S + 1)^C` with targets `t_x` and an integer radius
`R ≥ 1` such that `x ∈ L(V)` implies `dist(t_x, 𝒞) ≤ R` and `x ∉ L(V)` implies
`dist(t_x, 𝒞) > M^{1 - ε} · R`. -/
theorem exists_code_gap (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℕ, ∀ V : QuadraticVerifier p, Nonempty (CodeGap F ε V.Language (V.S + 1) C) :=
  ⟨_, code_gap p F ε hε hε1⟩

/-! ### Theorem 5.1 for lattices -/

/-- A fixed lattice with gap `M^{1/s - ε}` in `ℓ_p` for a language `Lang ⊆ X` with size
parameter `n` and exponent `C` (the conclusion of Theorem 5.1 for lattices, together with the
search test of Lemma 5.2): a full-rank lattice `Λ ⊆ ℤ^M` (containing `N · ℤ^M`) with
`1 ≤ M ≤ n^C`, integer targets `t_x` and an integer radius `R ≥ 1` such that `x ∈ Lang` implies
`dist_p(t_x, Λ) ≤ R` and `x ∉ Lang` implies `dist_p(t_x, Λ) > M^{1/s - ε} · R`; and a test
accepting every `M^{1/s-ε}`-approximate solution on `x ∈ Lang` and rejecting every vector on
`x ∉ Lang`. -/
structure LatticeGap (pn : PNorm) (ε : ℝ) {X : Type} (Lang : Set X) (n C : ℕ) where
  /-- The fixed lattice and the targets. -/
  Λ : LatticeFamily X
  /-- The radius. -/
  R : ℕ
  one_le_R : 1 ≤ R
  one_le_card : 1 ≤ Fintype.card Λ.M
  card_le : Fintype.card Λ.M ≤ n ^ C
  /-- The lattice contains `N · ℤ^M`. -/
  N : ℕ
  N_pos : 0 < N
  smul_mem : ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice
  yes : ∀ x ∈ Lang, Λ.latticeDist pn x ≤ R
  no : ∀ x ∉ Lang, (Fintype.card Λ.M : ℝ) ^ (1 / pn.s - ε) * R < Λ.latticeDist pn x
  /-- The test of Lemma 5.2. -/
  accepts : X → (Λ.M → ℤ) → Prop
  accepts_of_isApprox : ∀ x ∈ Lang, ∀ v ∈ Λ.lattice,
    Λ.dist pn x v ≤ (Fintype.card Λ.M : ℝ) ^ (1 / pn.s - ε) * Λ.latticeDist pn x → accepts x v
  not_accepts : ∀ x ∉ Lang, ∀ v, ¬ accepts x v

namespace LatticeGap

variable {pn : PNorm} {ε : ℝ} {X : Type} {Lang : Set X} {n C : ℕ} (G : LatticeGap pn ε Lang n C)

/-- The real image of the lattice is a full-rank lattice in Mathlib's sense. -/
theorem isZLattice : IsZLattice ℝ G.Λ.realLattice :=
  G.Λ.isZLattice_realLattice G.N_pos G.smul_mem

/-- Some lattice vector is within distance `R` of the target of a YES instance. -/
theorem exists_dist_le {x : X} (hx : x ∈ Lang) : ∃ v ∈ G.Λ.lattice, G.Λ.dist pn x v ≤ G.R := by
  obtain ⟨v, hv, hd⟩ := G.Λ.exists_dist_eq_latticeDist pn x
  exact ⟨v, hv, hd ▸ G.yes x hx⟩

/-- Every lattice vector is far from the target of a NO instance. -/
theorem lt_dist {x : X} (hx : x ∉ Lang) {v : G.Λ.M → ℤ} (hv : v ∈ G.Λ.lattice) :
    (Fintype.card G.Λ.M : ℝ) ^ (1 / pn.s - ε) * G.R < G.Λ.dist pn x v :=
  (G.no x hx).trans_le (G.Λ.latticeDist_le pn x hv)

/-- Transport a fixed lattice gap along a map of instances that respects the languages. -/
def comap {Y : Type} {Lang' : Set Y} (f : Y → X) (hf : ∀ y, f y ∈ Lang ↔ y ∈ Lang')
    {n' C' : ℕ} (hn : n ^ C ≤ n' ^ C') : LatticeGap pn ε Lang' n' C' where
  Λ := { M := G.Λ.M, lattice := G.Λ.lattice, target := fun y => G.Λ.target (f y) }
  R := G.R
  one_le_R := G.one_le_R
  one_le_card := G.one_le_card
  card_le := G.card_le.trans hn
  N := G.N
  N_pos := G.N_pos
  smul_mem := G.smul_mem
  yes := fun y hy => G.yes (f y) ((hf y).mpr hy)
  no := fun y hy => G.no (f y) (fun h => hy ((hf y).mp h))
  accepts := fun y v => G.accepts (f y) v
  accepts_of_isApprox := fun y hy v hv h => G.accepts_of_isApprox (f y) ((hf y).mpr hy) v hv h
  not_accepts := fun y hy v => G.not_accepts (f y) (fun h => hy ((hf y).mp h)) v

end LatticeGap

/-- **Theorem 5.1 for lattices**, with the explicit exponent `C = sizeExp 2 (1 - s ε)`: for every
norm exponent `1 ≤ p ≤ ∞` with `s = min {p, 2}`, every `0 < ε < 1/s` and every quadratic
verifier `V` over `𝔽_2`, there is a fixed full-rank lattice `Λ ⊆ ℤ^M` with `M ≤ (S + 1)^C` and
gap `M^{1/s - ε}` for `L(V)`. -/
theorem lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s)
    (V : QuadraticVerifier 2) :
    Nonempty (LatticeGap pn ε V.Language (V.S + 1) (sizeExp 2 (1 - pn.s * ε))) := by
  have hs1 := pn.one_le_s
  have hs2 := pn.s_le_two
  have hs0 : 0 < pn.s := by linarith
  set δ : ℝ := 1 - pn.s * ε with hδ
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    have := (lt_div_iff₀ hs0).mp hε1
    linarith
  have hδ1 : δ < 1 := by rw [hδ]; nlinarith
  have hm := (momentAxes_spec hδ1).1
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  obtain ⟨⟨L, hL, hgb, -, hDpos, hsize⟩⟩ := exists_gapReduction 2 V ((V.S + 1) ^ gapExp 2 δ)
    (momentAxes δ) (Nat.one_le_pow _ _ (by omega)) hm
  set n := Fintype.card L.ι with hn
  have hn1 : 1 ≤ n := by
    rw [hn, L.card_ι]
    exact Nat.mul_pos hDpos (by omega)
  obtain ⟨h64, hC⟩ := params_spec 2 hδ0 hδ1 V.S n hS1 hn1 hsize
  set g := (V.S + 1) ^ gapExp 2 δ with hg
  obtain ⟨Red⟩ := exists_latticeReduction L hgb hDpos pn
  set Λ := Red.Λ with hΛ
  have hM4 : Fintype.card Λ.M ≤ 4 * n := Red.card_lt_four_mul.le
  have h2n : 2 * n ≤ Fintype.card Λ.M := Red.two_mul_card_le
  have hMδ : 16 * (Fintype.card Λ.M : ℝ) ^ δ ≤ g := rpow_le_of_le_four_mul hδ0 hδ1.le hM4 h64
  have hexp : δ * (pn.s)⁻¹ = 1 / pn.s - ε := by rw [hδ]; field_simp
  have hMpos : (0 : ℝ) ≤ Fintype.card Λ.M := by positivity
  -- `M^{1/s - ε}` raised to the `s`-th power is `M^δ`
  have hfs : ((Fintype.card Λ.M : ℝ) ^ (1 / pn.s - ε)) ^ pn.s = (Fintype.card Λ.M : ℝ) ^ δ := by
    rw [← hexp, ← Real.rpow_mul hMpos, inv_mul_cancel_right₀ hs0.ne']
  have hRR : (0 : ℝ) < Red.R := by exact_mod_cast Red.one_le_R
  have hDR : (0 : ℝ) < L.numBlocks := by exact_mod_cast hDpos
  -- NO instances: every lattice vector is far from the target
  have hno : ∀ x ∉ V.Language, ∀ v ∈ Λ.lattice,
      (Fintype.card Λ.M : ℝ) ^ (1 / pn.s - ε) * Red.R < Λ.dist pn x v := by
    intro x hx v hv
    have hgw : (g : ℝ) * L.numBlocks < Red.weight x v := by
      exact_mod_cast Red.lt_weight x (hL.2 x hx) v hv
    have hdist0 : 0 ≤ Λ.dist pn x v := pn.norm_nonneg _
    -- `g D < w ≤ 16 D (dist/R)^s`, hence `g / 16 < (dist/R)^s`
    have h1 : (g : ℝ) < 16 * (Λ.dist pn x v / Red.R) ^ pn.s := by
      have : (g : ℝ) * L.numBlocks < 16 * (Λ.dist pn x v / Red.R) ^ pn.s * L.numBlocks := by
        calc (g : ℝ) * L.numBlocks < Red.weight x v := hgw
          _ ≤ 16 * L.numBlocks * (Λ.dist pn x v / Red.R) ^ pn.s := Red.weight_le x v hv
          _ = 16 * (Λ.dist pn x v / Red.R) ^ pn.s * L.numBlocks := by ring
      exact lt_of_mul_lt_mul_right this hDR.le
    have h2 : (Fintype.card Λ.M : ℝ) ^ δ < (Λ.dist pn x v / Red.R) ^ pn.s := by linarith
    -- take `(1/s)`-th powers
    have h3 : ((Fintype.card Λ.M : ℝ) ^ δ) ^ (pn.s)⁻¹ <
        ((Λ.dist pn x v / Red.R) ^ pn.s) ^ (pn.s)⁻¹ :=
      Real.rpow_lt_rpow (by positivity) h2 (by positivity)
    rw [Real.rpow_rpow_inv (by positivity) hs0.ne', ← Real.rpow_mul (by positivity)] at h3
    rw [hexp, lt_div_iff₀ hRR] at h3
    exact h3
  refine ⟨⟨Λ, Red.R, Red.one_le_R, by omega, by omega, Red.N, Red.N_pos, Red.smul_mem,
    fun x hx => Λ.latticeDist_le_of_exists pn x (Red.yes x (hL.1 x hx)),
    fun x hx => Λ.lt_latticeDist_of_forall pn x (hno x hx), Red.Accepts, ?_, ?_⟩⟩
  · intro x hx v hv happrox
    exact Red.accepts_of_isApprox (by positivity) (by rw [hfs]; exact hMδ) (hL.1 x hx) ⟨hv, happrox⟩
  · intro x hx v
    exact Red.not_accepts_of_isNo (hL.2 x hx) v

/-- **Theorem 5.1 for lattices**, paper form: for every norm exponent `1 ≤ p ≤ ∞` with
`s = min {p, 2}` and every `0 < ε < 1/s`, there is a constant `C` such that every quadratic
verifier `V` over `𝔽_2` admits a fixed full-rank lattice `Λ ⊆ ℤ^M` with `M ≤ (S + 1)^C`, integer
targets `t_x` and an integer radius `R ≥ 1` such that `x ∈ L(V)` implies `dist_p(t_x, Λ) ≤ R`
and `x ∉ L(V)` implies `dist_p(t_x, Λ) > M^{1/s - ε} · R`. -/
theorem exists_lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ V : QuadraticVerifier 2, Nonempty (LatticeGap pn ε V.Language (V.S + 1) C) :=
  ⟨_, lattice_gap pn ε hε hε1⟩

end LatticePrepro
