import LatticePrepro.Reduction.Soundness
import LatticePrepro.Tables.Explicit
import LatticePrepro.Conversions.Codes
import LatticePrepro.Conversions.Lattices

/-!
# Main results

* **Theorem 4.7** (`exists_gapReduction`): for every prime `p`, quadratic verifier `V` with `S`
  coordinates, gap `g ≥ 1` and `m ≥ 1`, there is a linear system family over `𝔽_p` that is a gap
  reduction from the language of `V` with gap `g`, with `g < b` and
  `n^m ≤ (8 p^4 m (S+1))^{(m+7) m} · g^{m+1}` columns.
* **Theorem 5.1** (`exists_code_gap`, `exists_lattice_gap`): fixed codes over any finite field,
  and fixed lattices in any `ℓ_p` norm, with polynomial dimension and approximation gap
  `M^{1/s - ε}`.

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

/-! ### The least admissible base `B` -/

/-- There is `B ≥ 2` with `Y ≤ B^m ≤ 2^m · Y` (the least `B ≥ 2` with `B^m ≥ Y`). -/
lemma exists_base {Y m : ℕ} (hm : 1 ≤ m) (hY : 1 ≤ Y) :
    ∃ B : ℕ, 2 ≤ B ∧ Y ≤ B ^ m ∧ B ^ m ≤ 2 ^ m * Y := by
  classical
  have hex : ∃ B : ℕ, 2 ≤ B ∧ Y ≤ B ^ m :=
    ⟨Y + 2, by omega, le_trans (by omega) (Nat.le_self_pow (by omega) (Y + 2))⟩
  set B := Nat.find hex with hBdef
  have hP : 2 ≤ B ∧ Y ≤ B ^ m := Nat.find_spec hex
  refine ⟨B, hP.1, hP.2, ?_⟩
  rcases Nat.lt_or_ge 2 B with h2 | h2
  · -- `B ≥ 3`: minimality gives `(B - 1)^m < Y`
    have hmin : ¬ (2 ≤ B - 1 ∧ Y ≤ (B - 1) ^ m) := Nat.find_min hex (by omega)
    have hlt : (B - 1) ^ m < Y := by
      by_contra hcon
      exact hmin ⟨by omega, not_lt.mp hcon⟩
    calc B ^ m ≤ (2 * (B - 1)) ^ m := Nat.pow_le_pow_left (by omega) m
      _ = 2 ^ m * (B - 1) ^ m := by rw [mul_pow]
      _ ≤ 2 ^ m * Y := Nat.mul_le_mul_left _ hlt.le
  · have hB2 : B = 2 := le_antisymm h2 hP.1
    rw [hB2]
    exact Nat.le_mul_of_pos_right _ hY

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

/-- **Theorem 4.7** (size and gap), existence form. -/
theorem exists_gapReduction (p : ℕ) [hp : Fact p.Prime] (V : QuadraticVerifier p) (g m : ℕ)
    (hg : 1 ≤ g) (hm : 1 ≤ m) :
    ∃ L : LinearSystemFamily (ZMod p) (Fin V.n → Bool),
      L.IsGapReduction V.Language g ∧ g < L.blockSize ∧
      (∃ e : ℕ, L.blockSize = p ^ e) ∧ 0 < L.numBlocks ∧
      (Fintype.card L.ι) ^ m ≤ (8 * p ^ 4 * m * (V.S + 1)) ^ ((m + 7) * m) * g ^ (m + 1) := by
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
  obtain ⟨K, _, _, ε', R, q, hr, hD, hb, ⟨d, hd, hqd⟩, hBq, hqlt⟩ :=
    exists_explicit_momentRepresentation p S' m B hS'2 hm hB2
  let ε : EncodingTuple p K V.S := ε'.castLE hSS'
  refine ⟨fixedSystem V R ε, ?_, ?_, ⟨d * m, ?_⟩, ?_, ?_⟩
  · -- gap reduction: `2 g N < r = B^m`
    apply FixedSystem.isGapReduction
    rw [hr]
    calc 2 * g * N < 8 * N * g := by nlinarith
      _ ≤ B ^ m := hYB
  · -- `g < b = q^m`
    show g < R.blockSize
    rw [hb]
    calc g < 8 * N * g := by nlinarith
      _ ≤ B ^ m := hYB
      _ ≤ q ^ m := Nat.pow_le_pow_left hBq m
  · show R.blockSize = p ^ (d * m)
    rw [hb, hqd, ← pow_mul]
  · -- the number of blocks `N · D` is positive
    rw [FixedSystem.numBlocks_eq]
    exact Nat.mul_pos hN1 R.numBlocks_pos
  · -- the size bound
    have hcard : Fintype.card (FixedSystem.Col V R) = N * q ^ (m + 1) := by
      rw [Fintype.card_prod, R.card_ι, hD, hb]; ring
    show Fintype.card (FixedSystem.Col V R) ^ m ≤ _
    rw [hcard]
    refine size_bound_aux (B := B) hp2 hm hS1 hNle ?_ ?_
    · calc q ≤ 8 * p ^ 3 * m * S' * B := hqlt.le
        _ ≤ 8 * p ^ 3 * m * (V.S + 1) * B := by gcongr
    · calc B ^ m ≤ 2 ^ m * (8 * N * g) := hBY
        _ ≤ p ^ m * (8 * N * g) := by gcongr

/-! ### Choice of parameters for Theorem 5.1 -/

/-- Parameter choice: given `0 ≤ δ < 1`, there are `m, k, C` such that for every `S ≥ 1`,
with `g = (S+1)^k`, any `n ≥ 1` with `n^m ≤ (8 p^4 m (S+1))^{(m+7) m} g^{m+1}` satisfies
`64 · n^δ ≤ g` and `4 n ≤ (S+1)^C`. -/
lemma exists_params (p : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∃ m k C : ℕ, 1 ≤ m ∧ ∀ S n : ℕ, 1 ≤ S → 1 ≤ n →
      n ^ m ≤ (8 * p ^ 4 * m * (S + 1)) ^ ((m + 7) * m) * ((S + 1) ^ k) ^ (m + 1) →
      64 * (n : ℝ) ^ δ ≤ ((S + 1) ^ k : ℕ) ∧ 4 * n ≤ (S + 1) ^ C := by
  -- choose `m` with `δ (1 + 1/m) < 1`
  obtain ⟨m, hm1, hmδ⟩ : ∃ m : ℕ, 1 ≤ m ∧ δ * (m + 1) < m := by
    obtain ⟨m, hm⟩ := exists_nat_gt (δ / (1 - δ))
    refine ⟨m + 1, by omega, ?_⟩
    have h1δ : 0 < 1 - δ := by linarith
    rw [div_lt_iff₀ h1δ] at hm
    push_cast
    nlinarith
  set a : ℕ := (8 * p ^ 4 * m + 1) * ((m + 7) * m) with ha
  set η : ℝ := m - δ * (m + 1) with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  set k : ℕ := ⌈(6 * m + a : ℝ) / η⌉₊ + 1 with hk
  refine ⟨m, k, a + k * (m + 1) + 2, hm1, ?_⟩
  intro S n hS hn hbound
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
      _ = (S + 1) ^ (a + k * (m + 1)) := by rw [ha, ← pow_mul, ← pow_mul, ← pow_add]
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
      have h2 : (⌈(6 * m + a : ℝ) / η⌉₊ : ℝ) ≤ k := by rw [hk]; push_cast; linarith
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

/-! ### Theorem 5.1 -/

/-- From the parameter choice: `M^δ ≤ g` whenever `M ≤ 4 n` and `64 n^δ ≤ g`. -/
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

/-- **Theorem 5.1 for codes**: for every finite field `F` of characteristic `p` and every
`0 < ε < 1`, there is a constant `C` such that every quadratic verifier `V` over `𝔽_p` admits a
fixed code of block length `M ≤ (S + 1)^C` with targets `t_x` and an integer radius `R ≥ 1`
such that `x ∈ L(V)` implies `dist(t_x, 𝒞) ≤ R` and `x ∉ L(V)` implies
`dist(t_x, 𝒞) > M^{1 - ε} · R`. -/
theorem exists_code_gap (p : ℕ) [hp : Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [DecidableEq F] [Algebra (ZMod p) F] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℕ, ∀ V : QuadraticVerifier p,
      ∃ (𝒞 : CodeFamily F (Fin V.n → Bool)) (R : ℕ),
        1 ≤ R ∧ 1 ≤ Fintype.card 𝒞.M ∧ Fintype.card 𝒞.M ≤ (V.S + 1) ^ C ∧
        ∀ x, (x ∈ V.Language → CodeFamily.codeDist (𝒞.target x) 𝒞.code ≤ R) ∧
          (x ∉ V.Language →
            (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) * R < CodeFamily.codeDist (𝒞.target x) 𝒞.code) := by
  obtain ⟨m, k, C, hm, hparams⟩ :=
    exists_params p (δ := 1 - ε) (by linarith) (by linarith)
  refine ⟨C, fun V => ?_⟩
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  obtain ⟨L, hL, hgb, -, hDpos, hsize⟩ :=
    exists_gapReduction p V ((V.S + 1) ^ k) m (Nat.one_le_pow _ _ (by omega)) hm
  set g := (V.S + 1) ^ k with hg
  set n := Fintype.card L.ι with hn
  have hn1 : 1 ≤ n := by
    rw [hn, L.card_ι]
    exact Nat.mul_pos hDpos (by omega)
  obtain ⟨h64, hC⟩ := hparams V.S n hS1 hn1 hsize
  -- the code over `F`
  refine ⟨(L.toCodeFamily).extend F, L.numBlocks, hDpos, ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · show 1 ≤ Fintype.card (L.ι ⊕ L.ι)
    rw [Fintype.card_sum]; omega
  · show Fintype.card (L.ι ⊕ L.ι) ≤ (V.S + 1) ^ C
    rw [Fintype.card_sum]; omega
  · intro hx
    show CodeFamily.codeDist ((L.toCodeFamily.extend F).target x) (L.toCodeFamily.extend F).code ≤ _
    rw [CodeFamily.codeDist_extend]
    exact L.codeDist_le_of_yes (hL.1 x hx)
  · intro hx
    show (Fintype.card (L.ι ⊕ L.ι) : ℝ) ^ (1 - ε) * (L.numBlocks : ℝ) <
      (CodeFamily.codeDist ((L.toCodeFamily.extend F).target x) (L.toCodeFamily.extend F).code : ℝ)
    rw [CodeFamily.codeDist_extend]
    have hlt : g * L.numBlocks < CodeFamily.codeDist (L.codeTarget x) L.code :=
      L.lt_codeDist_of_no hgb hDpos (hL.2 x hx)
    have hM : Fintype.card (L.ι ⊕ L.ι) ≤ 4 * n := by rw [Fintype.card_sum]; omega
    have hMδ := rpow_le_of_le_four_mul (M := Fintype.card (L.ι ⊕ L.ι)) (by linarith) (by linarith)
      hM h64
    have hDR : (0 : ℝ) < L.numBlocks := by exact_mod_cast hDpos
    calc (Fintype.card (L.ι ⊕ L.ι) : ℝ) ^ (1 - ε) * (L.numBlocks : ℝ)
        ≤ (g : ℝ) * L.numBlocks := by
          gcongr
          linarith [Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card (L.ι ⊕ L.ι))) (1 - ε)]
      _ < CodeFamily.codeDist (L.codeTarget x) L.code := by exact_mod_cast hlt

/-! #### Lattices -/

lemma PNorm.one_le_s (pn : PNorm) : 1 ≤ pn.s := by
  cases pn with
  | fin p hp => exact le_min hp (by norm_num)
  | inf => norm_num [PNorm.s]

lemma PNorm.s_le_two (pn : PNorm) : pn.s ≤ 2 := by
  cases pn with
  | fin p hp => exact min_le_right _ _
  | inf => norm_num [PNorm.s]

lemma PNorm.norm_nonneg {M : Type} [Fintype M] (pn : PNorm) (v : M → ℝ) : 0 ≤ pn.norm v := by
  cases pn with
  | fin p hp =>
      show 0 ≤ (∑ i, |v i| ^ p) ^ (1 / p)
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) _
  | inf =>
      show 0 ≤ ⨆ i, |v i|
      exact Real.iSup_nonneg fun i => abs_nonneg _

/-- **Theorem 5.1 for lattices**: for every norm exponent `1 ≤ p ≤ ∞` with `s = min {p, 2}` and
every `0 < ε < 1/s`, there is a constant `C` such that every quadratic verifier `V` over `𝔽_2`
admits a fixed full-rank lattice `Λ ⊆ ℤ^M` with `M ≤ (S + 1)^C`, integer targets `t_x` and an
integer radius `R ≥ 1` such that `x ∈ L(V)` implies some lattice vector is within `ℓ_p`-distance
`R` of `t_x`, and `x ∉ L(V)` implies every lattice vector is at distance more than
`M^{1/s - ε} · R`. -/
theorem exists_lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s) :
    ∃ C : ℕ, ∀ V : QuadraticVerifier 2,
      ∃ (Λ : LatticeFamily (Fin V.n → Bool)) (R : ℕ),
        1 ≤ R ∧ 1 ≤ Fintype.card Λ.M ∧ Fintype.card Λ.M ≤ (V.S + 1) ^ C ∧
        (∃ N : ℕ, 0 < N ∧ ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice) ∧
        ∀ x, (x ∈ V.Language → ∃ v ∈ Λ.lattice, Λ.dist pn x v ≤ R) ∧
          (x ∉ V.Language → ∀ v ∈ Λ.lattice,
            (Fintype.card Λ.M : ℝ) ^ (1 / pn.s - ε) * R < Λ.dist pn x v) := by
  have hs1 := pn.one_le_s
  have hs2 := pn.s_le_two
  have hs0 : 0 < pn.s := by linarith
  set δ : ℝ := 1 - pn.s * ε with hδ
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    have := (lt_div_iff₀ hs0).mp hε1
    linarith
  have hδ1 : δ < 1 := by rw [hδ]; nlinarith
  obtain ⟨m, k, C, hm, hparams⟩ := exists_params 2 hδ0 hδ1
  refine ⟨C, fun V => ?_⟩
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  obtain ⟨L, hL, hgb, -, hDpos, hsize⟩ :=
    exists_gapReduction 2 V ((V.S + 1) ^ k) m (Nat.one_le_pow _ _ (by omega)) hm
  set g := (V.S + 1) ^ k with hg
  set n := Fintype.card L.ι with hn
  have hn1 : 1 ≤ n := by
    rw [hn, L.card_ι]
    exact Nat.mul_pos hDpos (by omega)
  obtain ⟨h64, hC⟩ := hparams V.S n hS1 hn1 hsize
  obtain ⟨Λ, R, hR1, hRM, hM2n, hM4n, hfull, hyes, hno⟩ := exists_latticeFamily L hgb hDpos pn
  refine ⟨Λ, R, hR1, by omega, by omega, hfull, fun x => ⟨fun hx => hyes x (hL.1 x hx), ?_⟩⟩
  intro hx v hv
  obtain ⟨w, hw, hwno⟩ := hno x v hv
  have hgw := hwno (hL.2 x hx)
  -- `g D < w ≤ 16 D (dist/R)^s`, hence `g / 16 < (dist/R)^s`
  have hDR : (0 : ℝ) < L.numBlocks := by exact_mod_cast hDpos
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR1
  have hdist0 : 0 ≤ Λ.dist pn x v := pn.norm_nonneg _
  have hgwR : (g : ℝ) * L.numBlocks < w := by exact_mod_cast hgw
  have h1 : (g : ℝ) < 16 * (Λ.dist pn x v / R) ^ pn.s := by
    have : (g : ℝ) * L.numBlocks < 16 * (Λ.dist pn x v / R) ^ pn.s * L.numBlocks := by
      calc (g : ℝ) * L.numBlocks < w := hgwR
        _ ≤ 16 * L.numBlocks * (Λ.dist pn x v / R) ^ pn.s := hw
        _ = 16 * (Λ.dist pn x v / R) ^ pn.s * L.numBlocks := by ring
    exact lt_of_mul_lt_mul_right this hDR.le
  -- `M^δ ≤ g / 16`
  have hMδ := rpow_le_of_le_four_mul (M := Fintype.card Λ.M) hδ0 hδ1.le (by omega) h64
  have h2 : (Fintype.card Λ.M : ℝ) ^ δ < (Λ.dist pn x v / R) ^ pn.s := by linarith
  -- take `(1/s)`-th powers
  have h3 : ((Fintype.card Λ.M : ℝ) ^ δ) ^ (pn.s)⁻¹ < ((Λ.dist pn x v / R) ^ pn.s) ^ (pn.s)⁻¹ :=
    Real.rpow_lt_rpow (by positivity) h2 (by positivity)
  rw [Real.rpow_rpow_inv (by positivity) hs0.ne', ← Real.rpow_mul (by positivity)] at h3
  have hexp : δ * (pn.s)⁻¹ = 1 / pn.s - ε := by
    rw [hδ]; field_simp
  rw [hexp, lt_div_iff₀ hRR] at h3
  exact h3

end LatticePrepro
