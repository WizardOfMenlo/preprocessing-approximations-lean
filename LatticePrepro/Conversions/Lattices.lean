import LatticePrepro.Conversions.Codes
import LatticePrepro.Conversions.LpNorm
import LatticePrepro.Conversions.Hadamard
import LatticePrepro.Conversions.ConstructionA
import LatticePrepro.Conversions.Padding

/-!
# From codes to lattices (Lemma 3.8, Appendix B.2–B.3)

* `ℓ_p` norms on `M → ℝ` for `1 ≤ p < ∞` and `p = ∞` (`PNorm`).
* Construction A: `Λ_𝒞 = {v ∈ ℤ^M : v mod p ∈ 𝒞}` (Lemma B.2).
* The block Hadamard map (Lemma B.3): for `2 ≤ p ≤ ∞`, multiply lattice and target by a
  block-diagonal matrix of Sylvester–Hadamard matrices.
* The lattice reduction (Lemma 3.8, `LatticeReduction`, `exists_latticeReduction`): a fixed
  lattice `Λ`, an integer radius `R`, targets `t_x` and a residual weight such that YES instances
  have a lattice vector within distance `R` and NO instances have every lattice vector at distance
  more than `(g / 16)^{1/s} · R`, where `s = min {p, 2}`.
-/

namespace LatticePrepro

/-- A norm exponent: a real `p ≥ 1`, or `∞`. -/
inductive PNorm
  | fin (p : ℝ) (hp : 1 ≤ p)
  | inf

namespace PNorm

/-- The `ℓ_p` norm of a real vector. -/
noncomputable def norm {M : Type} [Fintype M] : PNorm → (M → ℝ) → ℝ
  | fin p _ => fun v => (∑ i, |v i| ^ p) ^ (1 / p)
  | inf => fun v => ⨆ i, |v i|

/-- The exponent `s = min {p, 2}` (`s = 2` for `p = ∞`). -/
noncomputable def s : PNorm → ℝ
  | fin p _ => min p 2
  | inf => 2

lemma one_le_s (pn : PNorm) : 1 ≤ pn.s := by
  cases pn with
  | fin p hp => exact le_min hp (by norm_num)
  | inf => norm_num [PNorm.s]

lemma s_le_two (pn : PNorm) : pn.s ≤ 2 := by
  cases pn with
  | fin p hp => exact min_le_right _ _
  | inf => norm_num [PNorm.s]

lemma norm_nonneg {M : Type} [Fintype M] (pn : PNorm) (v : M → ℝ) : 0 ≤ pn.norm v := by
  cases pn with
  | fin p hp =>
      show 0 ≤ (∑ i, |v i| ^ p) ^ (1 / p)
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) _
  | inf =>
      show 0 ≤ ⨆ i, |v i|
      exact Real.iSup_nonneg fun i => abs_nonneg _

end PNorm

/-- A fixed lattice `Λ ⊆ ℤ^M` with an integer target for every instance. -/
structure LatticeFamily (X : Type) where
  /-- Coordinates. -/
  M : Type
  [fintypeM : Fintype M]
  [decEqM : DecidableEq M]
  /-- The lattice, as a `ℤ`-submodule of `ℤ^M`. -/
  lattice : Submodule ℤ (M → ℤ)
  /-- The target for instance `x`. -/
  target : X → (M → ℤ)

namespace LatticeFamily

attribute [instance] fintypeM decEqM

variable {X : Type} (Λ : LatticeFamily X)

/-- The real vector of an integer vector. -/
def toReal {M : Type} (v : M → ℤ) : M → ℝ := fun i => (v i : ℝ)

/-- Distance in `ℓ_p` from the target to a lattice vector. -/
noncomputable def dist (pn : PNorm) (x : X) (v : Λ.M → ℤ) : ℝ :=
  pn.norm (toReal (Λ.target x - v))

end LatticeFamily


/-! ### Padding the code to blocks of size a power of two -/

section Padded

open Finset

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

namespace LinearSystemFamily

/-- `k` with `b ≤ 2^k < 2b`, where `b` is the block size. -/
noncomputable def padK : ℕ := Nat.clog 2 L.blockSize

lemma blockSize_le_two_pow_padK : L.blockSize ≤ 2 ^ L.padK := Nat.le_pow_clog one_lt_two _

lemma two_pow_padK_lt (hb : 1 ≤ L.blockSize) : 2 ^ L.padK < 2 * L.blockSize := by
  rcases Nat.lt_or_ge 1 L.blockSize with h | h
  · have h1 := Nat.pow_pred_clog_lt_self one_lt_two h
    have hk : 0 < L.padK := Nat.clog_pos one_lt_two h
    unfold padK at *
    rw [Nat.pred_eq_sub_one] at h1
    calc 2 ^ Nat.clog 2 L.blockSize = 2 * 2 ^ (Nat.clog 2 L.blockSize - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hk]
      _ < 2 * L.blockSize := by omega
  · have : L.blockSize = 1 := by omega
    simp [padK, this]

/-- Index set of a padded block. -/
abbrev PadIdx : Type := Hadamard.Idx L.padK

/-- Coordinates of the padded code: a block of the code and a position in `Fin k → ZMod 2`. -/
abbrev PadM : Type := (L.β ⊕ L.β) × L.PadIdx

lemma card_padM : Fintype.card L.PadM = 2 * L.numBlocks * 2 ^ L.padK := by
  simp only [Fintype.card_prod, Fintype.card_sum, Hadamard.card_Idx, numBlocks]
  ring

/-- An enumeration of the code coordinates. -/
noncomputable def codeEnum : (L.ι ⊕ L.ι) ≃ Fin (Fintype.card (L.ι ⊕ L.ι)) := Fintype.equivFin _

/-- The position of a coordinate inside its block. -/
noncomputable def codeRank (i : L.ι ⊕ L.ι) : ℕ :=
  (univ.filter fun j => L.codeBlk j = L.codeBlk i ∧ L.codeEnum j < L.codeEnum i).card

lemma codeRank_lt_blockSize (i : L.ι ⊕ L.ι) : L.codeRank i < L.blockSize := by
  calc L.codeRank i ≤ ((univ.filter fun j => L.codeBlk j = L.codeBlk i).erase i).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hj ⊢
        refine ⟨fun hji => ?_, hj.1⟩
        subst hji
        exact lt_irrefl _ hj.2
    _ < (univ.filter fun j => L.codeBlk j = L.codeBlk i).card :=
        Finset.card_erase_lt_of_mem (by simp)
    _ = L.blockSize := L.card_codeBlk_fiber _

lemma codeRank_lt_of_lt {i j : L.ι ⊕ L.ι} (hs : L.codeBlk i = L.codeBlk j)
    (hij : L.codeEnum i < L.codeEnum j) : L.codeRank i < L.codeRank j := by
  unfold codeRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, by simp [hs, hij], by simp⟩
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact ⟨hl.1.trans hs, hl.2.trans hij⟩

lemma codeRank_inj {i j : L.ι ⊕ L.ι} (hs : L.codeBlk i = L.codeBlk j)
    (hr : L.codeRank i = L.codeRank j) : i = j := by
  by_contra hne
  have hne' : L.codeEnum i ≠ L.codeEnum j := fun h => hne (L.codeEnum.injective h)
  rcases lt_or_gt_of_ne hne' with h | h
  · exact absurd hr (L.codeRank_lt_of_lt hs h).ne
  · exact absurd hr (L.codeRank_lt_of_lt hs.symm h).ne'

/-- Positions `Fin (2^k)` as elements of `Fin k → ZMod 2`. -/
noncomputable def padIdxEquiv : Fin (2 ^ L.padK) ≃ L.PadIdx :=
  (Fintype.equivFinOfCardEq (Hadamard.card_Idx L.padK)).symm

/-- The block-respecting embedding of the code coordinates into the padded coordinates. -/
noncomputable def padEmbFn (i : L.ι ⊕ L.ι) : L.PadM :=
  (L.codeBlk i, L.padIdxEquiv ⟨L.codeRank i,
    lt_of_lt_of_le (L.codeRank_lt_blockSize i) L.blockSize_le_two_pow_padK⟩)

lemma padEmbFn_injective : Function.Injective L.padEmbFn := by
  intro i j h
  simp only [padEmbFn, Prod.mk.injEq] at h
  obtain ⟨hs, he⟩ := h
  have := L.padIdxEquiv.injective he
  exact L.codeRank_inj hs (Fin.mk.inj_iff.mp this)

/-- The padding embedding. -/
noncomputable def padEmb : L.ι ⊕ L.ι ↪ L.PadM := ⟨L.padEmbFn, L.padEmbFn_injective⟩

lemma padEmb_fst (i : L.ι ⊕ L.ι) : (L.padEmb i).1 = L.codeBlk i := rfl

/-- The padded code. -/
noncomputable def padCode : Submodule (ZMod p) (L.PadM → ZMod p) :=
  Submodule.map (padMap L.padEmb) L.code

/-- The padded target. -/
noncomputable def padTarget (x : X) : L.PadM → ZMod p := padMap L.padEmb (L.codeTarget x)

/-- (B.1) for the padded code, YES instances. -/
theorem pad_yes {x : X} (hx : L.IsYes x) :
    ∃ e : L.PadM → ZMod p, IsBinary e ∧ AtMostOnePerBlock Prod.fst e ∧
      hammingNorm e ≤ L.numBlocks ∧ L.padTarget x - e ∈ L.padCode := by
  obtain ⟨e, hb, h1, hw, hmem⟩ := L.code_yes hx
  refine ⟨padMap L.padEmb e, isBinary_padMap _ hb,
    atMostOnePerBlock_padMap L.padEmb L.codeBlk Prod.fst L.padEmb_fst h1,
    by rw [hammingNorm_padMap]; exact hw, ?_⟩
  rw [padTarget, ← map_sub]
  exact Submodule.mem_map_of_mem hmem

/-- (B.1) for the padded code, NO instances. -/
theorem pad_no {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hx : L.IsNo g x) :
    ∀ c ∈ L.padCode, g * L.numBlocks < hammingDist (L.padTarget x) c := by
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := Submodule.mem_map.mp hc
  rw [padTarget, hammingDist_padMap]
  exact L.code_no hg hD hx c₀ hc₀

end LinearSystemFamily

end Padded

/-! ### Block-sparse binary vectors under the Hadamard map -/

section HadamardSparse

open Finset

variable {p : ℕ} [Fact p.Prime] {β : Type*} [Fintype β] [DecidableEq β] {k : ℕ}

/-- For a `{0,1}`-vector `ẽ` with at most one nonzero entry per block, `H ẽ` has entries of
absolute value at most `1`, supported on at most `2^k · wt(ẽ)` coordinates. -/
lemma blockHad_lift_bound {e : β × Hadamard.Idx k → ZMod p} (hb : IsBinary e)
    (h1 : AtMostOnePerBlock Prod.fst e) :
    (∀ su, |Hadamard.blockHad k (liftZMod e) su| ≤ 1) ∧
    (univ.filter fun su => Hadamard.blockHad k (liftZMod e) su ≠ 0).card ≤
      hammingNorm e * 2 ^ k := by
  -- the number of nonzero entries of `e` in block `s`
  have hblk : ∀ s : β, (univ.filter fun w => e (s, w) ≠ 0).card ≤ 1 := by
    intro s
    refine le_trans ?_ (h1 s)
    refine Finset.card_le_card_of_injOn (fun w => (s, w)) ?_ ?_
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_filter] at hw
      rw [Finset.mem_coe]
      simp [blockSupport, hw.2]
    · intro w _ w' _ h
      exact (Prod.mk.inj h).2
  have habs : ∀ i, |liftZMod e i| = if e i ≠ 0 then 1 else 0 := by
    intro i
    rcases liftZMod_binary hb i with h | h
    · rw [h, abs_zero]
      rw [(liftZMod_eq_zero_iff e i).mp h]
      simp
    · rw [h, abs_one]
      have : e i ≠ 0 := fun h0 => by
        rw [(liftZMod_eq_zero_iff e i).mpr h0] at h
        exact zero_ne_one h
      simp [this]
  refine ⟨fun su => ?_, ?_⟩
  · calc |Hadamard.blockHad k (liftZMod e) su| ≤ ∑ w, |liftZMod e (su.1, w)| :=
          Hadamard.abs_blockHad_le k _ su
      _ = ((univ.filter fun w => e (su.1, w) ≠ 0).card : ℤ) := by
          simp_rw [habs]
          rw [Finset.sum_boole]
      _ ≤ 1 := by exact_mod_cast hblk su.1
  · -- the support of `H ẽ` is contained in `{blocks of e that are nonzero} × univ`
    have hsub : (univ.filter fun su => Hadamard.blockHad k (liftZMod e) su ≠ 0) ⊆
        (univ.filter fun s : β => ∃ w, e (s, w) ≠ 0) ×ˢ univ := by
      intro su hsu
      simp only [mem_filter, mem_univ, true_and, mem_product, and_true] at hsu ⊢
      by_contra h
      simp only [not_exists, not_not] at h
      apply hsu
      apply Hadamard.blockHad_eq_zero_of_block
      intro w
      rw [liftZMod_eq_zero_iff]
      exact h w
    have hcard : (univ.filter fun s : β => ∃ w, e (s, w) ≠ 0).card ≤ hammingNorm e := by
      unfold hammingNorm
      calc (univ.filter fun s : β => ∃ w, e (s, w) ≠ 0).card
          ≤ ((univ.filter fun su : β × Hadamard.Idx k => e su ≠ 0).image Prod.fst).card := by
            apply Finset.card_le_card
            intro s hs
            simp only [mem_filter, mem_univ, true_and, mem_image] at hs ⊢
            obtain ⟨w, hw⟩ := hs
            exact ⟨(s, w), hw, rfl⟩
        _ ≤ (univ.filter fun su : β × Hadamard.Idx k => e su ≠ 0).card := Finset.card_image_le
    calc (univ.filter fun su => Hadamard.blockHad k (liftZMod e) su ≠ 0).card
        ≤ ((univ.filter fun s : β => ∃ w, e (s, w) ≠ 0) ×ˢ univ).card := Finset.card_le_card hsub
      _ = (univ.filter fun s : β => ∃ w, e (s, w) ≠ 0).card * 2 ^ k := by
          rw [Finset.card_product, Finset.card_univ, Hadamard.card_Idx]
      _ ≤ hammingNorm e * 2 ^ k := Nat.mul_le_mul_right _ hcard

end HadamardSparse

/-! ### Real-number bounds for the radius -/

section RealBounds

/-- Case `1 ≤ q ≤ 2`: with `R = ⌈D^{1/q}⌉`, `r^q ≤ 16 D (r / R)^q`. -/
lemma radius_bound_le_two {q D r : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hD : 1 ≤ D) (hr : 0 ≤ r) :
    r ^ q ≤ 16 * D * (r / (⌈D ^ (1 / q)⌉₊ : ℝ)) ^ q := by
  have hq0 : 0 < q := by linarith
  set R₀ : ℝ := D ^ (1 / q) with hR₀
  have hR₀1 : 1 ≤ R₀ := Real.one_le_rpow hD (by positivity)
  have hRpos : (0 : ℝ) < ⌈R₀⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr (by linarith)
  have hRle : (⌈R₀⌉₊ : ℝ) ≤ 2 * R₀ := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ R₀)
    linarith
  have hRq : (⌈R₀⌉₊ : ℝ) ^ q ≤ 4 * D := by
    calc (⌈R₀⌉₊ : ℝ) ^ q ≤ (2 * R₀) ^ q := Real.rpow_le_rpow hRpos.le hRle hq0.le
      _ = 2 ^ q * R₀ ^ q := Real.mul_rpow (by norm_num) (by linarith)
      _ = 2 ^ q * D := by
          rw [hR₀, ← Real.rpow_mul (by linarith), one_div_mul_cancel hq0.ne', Real.rpow_one]
      _ ≤ 4 * D := by
          have h2 : (2 : ℝ) ^ q ≤ 2 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
          rw [Real.rpow_two] at h2
          nlinarith
  rw [Real.div_rpow hr hRpos.le]
  have hRqpos : 0 < (⌈R₀⌉₊ : ℝ) ^ q := Real.rpow_pos_of_pos hRpos q
  have hrq : 0 ≤ r ^ q := Real.rpow_nonneg hr q
  rw [show 16 * D * (r ^ q / (⌈R₀⌉₊ : ℝ) ^ q) = r ^ q * (16 * D / (⌈R₀⌉₊ : ℝ) ^ q) by ring]
  have : 1 ≤ 16 * D / (⌈R₀⌉₊ : ℝ) ^ q := by
    rw [le_div_iff₀ hRqpos]
    linarith
  nlinarith

/-- Case `q > 2`: with `a = t · D`, `R = ⌈a^{1/q}⌉`, `w ≤ A / t` and the power-mean bound
`A ≤ (2a)^{1-2/q} B^{2/q}`, we get `w ≤ 16 D (B^{1/q} / R)^2`. -/
lemma radius_bound_gt_two {q t D A B w : ℝ} (hq : 2 < q) (ht : 1 ≤ t) (hD : 1 ≤ D)
    (hB : 0 ≤ B) (hw : w ≤ A / t) (hAB : A ≤ (2 * (t * D)) ^ (1 - 2 / q) * B ^ (2 / q)) :
    w ≤ 16 * D * (B ^ (1 / q) / (⌈(t * D) ^ (1 / q)⌉₊ : ℝ)) ^ (2 : ℝ) := by
  have hq0 : 0 < q := by linarith
  set a : ℝ := t * D with ha_def
  have ha : 1 ≤ a := by nlinarith
  have hapos : 0 < a := by linarith
  set R₀ : ℝ := a ^ (1 / q) with hR₀
  have hR₀1 : 1 ≤ R₀ := Real.one_le_rpow ha (by positivity)
  set R : ℝ := (⌈R₀⌉₊ : ℝ) with hR
  have hRpos : 0 < R := by rw [hR]; exact_mod_cast Nat.ceil_pos.mpr (by linarith)
  have hR₀R : R₀ ≤ R := Nat.le_ceil _
  have hR2 : R ≤ 2 * R₀ := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ R₀)
    rw [hR]; linarith
  have hR₀sq : R₀ ^ 2 = a ^ (2 / q) := by
    rw [hR₀, ← Real.rpow_natCast, ← Real.rpow_mul hapos.le]
    congr 1
    push_cast
    ring
  have hr2 : (B ^ (1 / q)) ^ 2 = B ^ (2 / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
    congr 1
    push_cast
    ring
  have hsub : a ^ (1 - 2 / q) = a / a ^ (2 / q) := by
    rw [Real.rpow_sub hapos, Real.rpow_one]
  have h1 : (2 * a) ^ (1 - 2 / q) ≤ 2 * (a / R₀ ^ 2) := by
    rw [Real.mul_rpow (by norm_num) hapos.le, hR₀sq, ← hsub]
    have h2 : (2 : ℝ) ^ (1 - 2 / q) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - 2 / q) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num)
              (by linarith [show (0 : ℝ) < 2 / q by positivity])
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hapos.le _)
  have hR₀pos : 0 < R₀ := by linarith
  have h2 : A ≤ 2 * (a / R₀ ^ 2) * (B ^ (1 / q)) ^ 2 := by
    rw [hr2]
    calc A ≤ (2 * a) ^ (1 - 2 / q) * B ^ (2 / q) := hAB
      _ ≤ 2 * (a / R₀ ^ 2) * B ^ (2 / q) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hB _)
  have h3 : w ≤ 2 * D * (B ^ (1 / q)) ^ 2 / R₀ ^ 2 := by
    calc w ≤ A / t := hw
      _ ≤ 2 * (a / R₀ ^ 2) * (B ^ (1 / q)) ^ 2 / t :=
          div_le_div_of_nonneg_right h2 (by linarith)
      _ = 2 * D * (B ^ (1 / q)) ^ 2 / R₀ ^ 2 := by
          rw [ha_def]
          field_simp
  have h4 : R ^ 2 ≤ 4 * R₀ ^ 2 := by nlinarith
  have hb2 : 0 ≤ (B ^ (1 / q)) ^ 2 := sq_nonneg _
  rw [Real.rpow_two, div_pow]
  calc w ≤ 2 * D * (B ^ (1 / q)) ^ 2 / R₀ ^ 2 := h3
    _ ≤ 8 * D * (B ^ (1 / q)) ^ 2 / R ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * D) hb2) (sub_nonneg.mpr h4)]
    _ ≤ 16 * D * ((B ^ (1 / q)) ^ 2 / R ^ 2) := by
        rw [mul_div_assoc]
        have : 0 ≤ (B ^ (1 / q)) ^ 2 / R ^ 2 := by positivity
        nlinarith

/-- Case `p = ∞`: with `R = 1`, `w ≤ A / t` and `A ≤ 2 t D m^2`, we get `w ≤ 16 D (m / 1)^2`. -/
lemma radius_bound_inf {t D A m w : ℝ} (ht : 0 < t) (hD : 0 ≤ D) (hw : w ≤ A / t)
    (hA : A ≤ 2 * (t * D) * m ^ 2) : w ≤ 16 * D * (m / ((1 : ℕ) : ℝ)) ^ (2 : ℝ) := by
  rw [Nat.cast_one, div_one, Real.rpow_two]
  have : A / t ≤ 2 * D * m ^ 2 := by
    rw [div_le_iff₀ ht]
    nlinarith
  nlinarith [sq_nonneg m]

end RealBounds

/-! ### The lattice reduction: statement -/

/-- The output of Lemma 3.8 for a linear system family `L`, a gap `g` and a norm exponent `pn`:
a fixed lattice `Λ ⊆ ℤ^M` with `2 n ≤ M < 4 n` (`n = |ι|`), containing `N · ℤ^M` for some
`N > 0` (full rank), an integer radius `1 ≤ R ≤ M`, and a *residual weight* `w = weight x v`
computable from a lattice vector `v`, such that

* YES instances have a lattice vector within `ℓ_p`-distance `R` of the target;
* `w ≤ 16 · D · (dist / R)^s` for every lattice vector, and `w > g · D` on NO instances.

The residual weight is the quantity tested in Lemma 5.2 (`Conversions/SearchTest.lean`). -/
structure LatticeReduction {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)
    (g : ℕ) (pn : PNorm) where
  /-- The fixed lattice and the targets. -/
  Λ : LatticeFamily X
  /-- The radius. -/
  R : ℕ
  one_le_R : 1 ≤ R
  R_le_card : R ≤ Fintype.card Λ.M
  two_mul_card_le : 2 * Fintype.card L.ι ≤ Fintype.card Λ.M
  card_lt_four_mul : Fintype.card Λ.M < 4 * Fintype.card L.ι
  /-- The lattice contains `N · ℤ^M`. -/
  N : ℕ
  N_pos : 0 < N
  smul_mem : ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice
  /-- The residual weight of a lattice vector. -/
  weight : X → (Λ.M → ℤ) → ℕ
  yes : ∀ x, L.IsYes x → ∃ v ∈ Λ.lattice, Λ.dist pn x v ≤ R
  weight_le : ∀ x, ∀ v ∈ Λ.lattice,
    (weight x v : ℝ) ≤ 16 * L.numBlocks * (Λ.dist pn x v / R) ^ pn.s
  lt_weight : ∀ x, L.IsNo g x → ∀ v ∈ Λ.lattice, g * L.numBlocks < weight x v

/-! ### The three cases of the lattice reduction -/

section Cases

open Finset

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

namespace LinearSystemFamily

/-- The Construction A lattice family on the padded code (for `p ≤ 2`). -/
noncomputable abbrev latticeA : LatticeFamily X where
  M := L.PadM
  lattice := constructionA L.padCode
  target := fun x => liftZMod (L.padTarget x)

/-- The residual weight for Construction A: `wt((t_x - v) mod p)`. -/
noncomputable def weightA (x : X) (v : L.PadM → ℤ) : ℕ :=
  hammingNorm (redMod p L.PadM (liftZMod (L.padTarget x) - v))

/-- The Hadamard-transformed lattice family (for `p > 2`). -/
noncomputable abbrev latticeH : LatticeFamily X where
  M := L.PadM
  lattice := Submodule.map (Hadamard.blockHadₗ L.padK) (constructionA L.padCode)
  target := fun x => Hadamard.blockHad L.padK (liftZMod (L.padTarget x))

/-- The residual weight for the Hadamard lattice: `wt((t_x - H⁻¹ v) mod p)`, where
`H⁻¹ v = 2^{-k} H v`. -/
noncomputable def weightH (x : X) (v : L.PadM → ℤ) : ℕ :=
  hammingNorm (redMod p L.PadM (liftZMod (L.padTarget x) - Hadamard.blockInv L.padK v))

lemma two_mul_card_le_card_padM : 2 * Fintype.card L.ι ≤ Fintype.card L.PadM := by
  rw [L.card_padM, L.card_ι, mul_assoc]
  exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ L.blockSize_le_two_pow_padK)

lemma card_padM_lt {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) :
    Fintype.card L.PadM < 4 * Fintype.card L.ι := by
  rw [L.card_padM, L.card_ι]
  have hk := L.two_pow_padK_lt (by omega)
  calc 2 * L.numBlocks * 2 ^ L.padK < 2 * L.numBlocks * (2 * L.blockSize) :=
        Nat.mul_lt_mul_of_pos_left hk (by omega)
    _ = 4 * (L.numBlocks * L.blockSize) := by ring

/-- NO instances for Construction A: the residual weight exceeds `g · D`. -/
lemma lt_weightA {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hno : L.IsNo g x) {v : L.PadM → ℤ} (hv : v ∈ L.latticeA.lattice) :
    g * L.numBlocks < L.weightA x v := by
  obtain ⟨hvC, hwt⟩ := redMod_lift_sub L.padCode (L.padTarget x) hv
  unfold weightA
  rw [hwt]
  exact L.pad_no hg hD hno _ hvC

/-- Case `1 ≤ q ≤ 2`. -/
noncomputable def reduction_le_two {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    {q : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2) : LatticeReduction L g (PNorm.fin q hq) := by
  have hq0 : 0 < q := by linarith
  have hD1 : (1 : ℝ) ≤ L.numBlocks := by exact_mod_cast hD
  set R₀ : ℝ := (L.numBlocks : ℝ) ^ (1 / q) with hR₀
  have hR₀1 : 1 ≤ R₀ := Real.one_le_rpow hD1 (by positivity)
  refine ⟨L.latticeA, ⌈R₀⌉₊, ?_, ?_, L.two_mul_card_le_card_padM, L.card_padM_lt hg hD,
    p, (Fact.out : p.Prime).pos, fun v => natCast_smul_mem_constructionA _ v, L.weightA, ?_, ?_,
    fun x hno v hv => L.lt_weightA hg hD hno hv⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  · rw [Nat.ceil_le]
    calc R₀ ≤ (L.numBlocks : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hD1 (by rw [div_le_one hq0]; exact hq)
      _ = (L.numBlocks : ℝ) := Real.rpow_one _
      _ ≤ (Fintype.card L.PadM : ℝ) := by
          rw [L.card_padM]
          have : 1 ≤ 2 ^ L.padK := Nat.one_le_two_pow
          exact_mod_cast (by nlinarith : L.numBlocks ≤ 2 * L.numBlocks * 2 ^ L.padK)
  · -- YES
    intro x hx
    obtain ⟨e, hb, h1, hw, hmem⟩ := L.pad_yes hx
    refine ⟨liftZMod (L.padTarget x) - liftZMod e,
      lift_sub_lift_mem_constructionA _ hmem, ?_⟩
    change lpNorm q (LatticeFamily.toReal
      (liftZMod (L.padTarget x) - (liftZMod (L.padTarget x) - liftZMod e))) ≤ (⌈R₀⌉₊ : ℝ)
    rw [sub_sub_cancel]
    refine le_trans (lpNorm_le_rpow_of_sum_le hq0 ?_) (Nat.le_ceil _)
    calc ∑ i, |LatticeFamily.toReal (liftZMod e) i| ^ q
        ≤ ((univ.filter fun i => LatticeFamily.toReal (liftZMod e) i ≠ 0).card : ℝ) := by
          refine sum_abs_rpow_le_card_ne_zero hq0 fun i => ?_
          simp only [LatticeFamily.toReal]
          rw [← Int.cast_abs]
          exact_mod_cast abs_liftZMod_le_one hb i
      _ = (hammingNorm e : ℝ) := by
          unfold hammingNorm
          congr 2
          ext i
          simp [LatticeFamily.toReal, liftZMod_eq_zero_iff]
      _ ≤ (L.numBlocks : ℝ) := by exact_mod_cast hw
  · -- the weight bound
    intro x v _
    have hs : (PNorm.fin q hq).s = q := min_eq_left hq2
    rw [hs]
    set d := liftZMod (L.padTarget x) - v with hd
    change (hammingNorm (redMod p L.PadM d) : ℝ) ≤
      16 * L.numBlocks * (lpNorm q (LatticeFamily.toReal d) / (⌈R₀⌉₊ : ℝ)) ^ q
    have hwd : (hammingNorm (redMod p L.PadM d) : ℝ) ≤ lpNorm q (LatticeFamily.toReal d) ^ q := by
      rw [lpNorm_rpow hq0]
      calc (hammingNorm (redMod p L.PadM d) : ℝ)
          ≤ ((univ.filter fun i => d i ≠ 0).card : ℝ) := by exact_mod_cast hammingNorm_redMod_le d
        _ ≤ ∑ i, |LatticeFamily.toReal d i| ^ q := card_ne_zero_le_sum_abs_rpow hq0.le d
    exact hwd.trans (radius_bound_le_two hq hq2 hD1 (lpNorm_nonneg _ _))

/-- The common data of the Hadamard cases: full rank, the YES bound and the NO bound. -/
lemma latticeH_smul_mem (v : L.PadM → ℤ) :
    ((p * 2 ^ L.padK : ℕ) : ℤ) • v ∈ L.latticeH.lattice := by
  refine Submodule.mem_map.mpr ⟨(p : ℤ) • Hadamard.blockHad L.padK v,
    natCast_smul_mem_constructionA _ _, ?_⟩
  rw [Hadamard.blockHadₗ_apply, Hadamard.blockHad_smul, Hadamard.blockHad_blockHad, smul_smul]
  push_cast
  rfl

/-- YES instances in the Hadamard cases: the residual `H ẽ` has entries of absolute value at
most `1` on at most `D · 2^k` coordinates. -/
lemma latticeH_yes {x : X} (hx : L.IsYes x) :
    ∃ v ∈ L.latticeH.lattice, (∀ su, |(L.latticeH.target x - v) su| ≤ 1) ∧
      (univ.filter fun su => (L.latticeH.target x - v) su ≠ 0).card ≤
        L.numBlocks * 2 ^ L.padK := by
  obtain ⟨e, hb, h1, hw, hmem⟩ := L.pad_yes hx
  refine ⟨Hadamard.blockHad L.padK (liftZMod (L.padTarget x) - liftZMod e),
    Submodule.mem_map_of_mem (lift_sub_lift_mem_constructionA _ hmem), ?_⟩
  have hres : L.latticeH.target x - Hadamard.blockHad L.padK (liftZMod (L.padTarget x) - liftZMod e)
      = Hadamard.blockHad L.padK (liftZMod e) := by
    show Hadamard.blockHad L.padK (liftZMod (L.padTarget x)) - _ = _
    rw [← Hadamard.blockHad_sub, sub_sub_cancel]
  rw [hres]
  obtain ⟨habs, hcard⟩ := blockHad_lift_bound hb h1
  exact ⟨habs, hcard.trans (Nat.mul_le_mul_right _ hw)⟩

/-- The residual weight of `v = H u` in the Hadamard lattice is `wt((t - u) mod p)`. -/
lemma weightH_blockHad (x : X) (u : L.PadM → ℤ) :
    L.weightH x (Hadamard.blockHad L.padK u) =
      hammingNorm (redMod p L.PadM (liftZMod (L.padTarget x) - u)) := by
  rw [weightH, Hadamard.blockInv_blockHad]

/-- The residual weight in the Hadamard cases satisfies `w ≤ ‖t_H - v‖₂² / 2^k`. -/
lemma weightH_le (x : X) {v : L.PadM → ℤ} (hv : v ∈ L.latticeH.lattice) :
    (L.weightH x v : ℝ) ≤ (∑ su, ((L.latticeH.target x - v) su : ℝ) ^ 2) / (2 ^ L.padK : ℝ) := by
  obtain ⟨u, -, rfl⟩ := Submodule.mem_map.mp hv
  rw [Hadamard.blockHadₗ_apply, weightH_blockHad]
  set d := liftZMod (L.padTarget x) - u with hd
  have hres : L.latticeH.target x - Hadamard.blockHad L.padK u = Hadamard.blockHad L.padK d := by
    show Hadamard.blockHad L.padK (liftZMod (L.padTarget x)) - _ = _
    rw [← Hadamard.blockHad_sub]
  rw [hres]
  have hpars : ∑ su, ((Hadamard.blockHad L.padK d su : ℤ) : ℝ) ^ 2 =
      (2 ^ L.padK : ℝ) * ∑ su, ((d su : ℤ) : ℝ) ^ 2 := by
    have := Hadamard.sum_sq_blockHad L.padK d
    exact_mod_cast this
  rw [hpars, mul_div_cancel_left₀ _ (by positivity)]
  calc (hammingNorm (redMod p L.PadM d) : ℝ)
      ≤ ((univ.filter fun i => d i ≠ 0).card : ℝ) := by exact_mod_cast hammingNorm_redMod_le d
    _ ≤ ∑ su, ((d su : ℤ) : ℝ) ^ 2 := card_ne_zero_le_sum_sq d

/-- NO instances in the Hadamard cases: the residual weight exceeds `g · D`. -/
lemma lt_weightH {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hno : L.IsNo g x) {v : L.PadM → ℤ} (hv : v ∈ L.latticeH.lattice) :
    g * L.numBlocks < L.weightH x v := by
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
  rw [Hadamard.blockHadₗ_apply, weightH_blockHad]
  obtain ⟨huC, hwt⟩ := redMod_lift_sub L.padCode (L.padTarget x) hu
  rw [hwt]
  exact L.pad_no hg hD hno _ huC

/-- Case `q > 2`. -/
noncomputable def reduction_gt_two {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    {q : ℝ} (hq : 1 ≤ q) (hq2 : 2 < q) : LatticeReduction L g (PNorm.fin q hq) := by
  have hq0 : 0 < q := by linarith
  have hD1 : (1 : ℝ) ≤ L.numBlocks := by exact_mod_cast hD
  have ht1 : (1 : ℝ) ≤ (2 ^ L.padK : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  set a : ℝ := (2 ^ L.padK : ℝ) * L.numBlocks with ha
  have ha1 : 1 ≤ a := by nlinarith
  set R₀ : ℝ := a ^ (1 / q) with hR₀
  have hR₀1 : 1 ≤ R₀ := Real.one_le_rpow ha1 (by positivity)
  have hcardR : (Fintype.card L.PadM : ℝ) = 2 * a := by
    rw [L.card_padM, ha]; push_cast; ring
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨L.latticeH, ⌈R₀⌉₊, ?_, ?_, L.two_mul_card_le_card_padM, L.card_padM_lt hg hD,
    p * 2 ^ L.padK, by positivity, L.latticeH_smul_mem, L.weightH, ?_, ?_,
    fun x hno v hv => L.lt_weightH hg hD hno hv⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  · change ⌈R₀⌉₊ ≤ Fintype.card L.PadM
    rw [Nat.ceil_le, hcardR]
    calc R₀ ≤ a ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ha1 (by rw [div_le_one hq0]; exact hq)
      _ = a := Real.rpow_one _
      _ ≤ 2 * a := by linarith
  · -- YES
    intro x hx
    obtain ⟨v, hv, habs, hcard⟩ := L.latticeH_yes hx
    refine ⟨v, hv, ?_⟩
    change lpNorm q (LatticeFamily.toReal (L.latticeH.target x - v)) ≤ (⌈R₀⌉₊ : ℝ)
    refine le_trans (lpNorm_le_rpow_of_sum_le hq0 ?_) (Nat.le_ceil _)
    calc ∑ i, |LatticeFamily.toReal (L.latticeH.target x - v) i| ^ q
        ≤ ((univ.filter fun i =>
            LatticeFamily.toReal (L.latticeH.target x - v) i ≠ 0).card : ℝ) := by
          refine sum_abs_rpow_le_card_ne_zero hq0 fun i => ?_
          simp only [LatticeFamily.toReal]
          rw [← Int.cast_abs]
          exact_mod_cast habs i
      _ = ((univ.filter fun su => (L.latticeH.target x - v) su ≠ 0).card : ℝ) := by
          congr 2
          ext i
          simp only [mem_filter, mem_univ, true_and, LatticeFamily.toReal, ne_eq, Int.cast_eq_zero]
      _ ≤ ((L.numBlocks * 2 ^ L.padK : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = a := by rw [ha]; push_cast; ring
  · -- the weight bound
    intro x v hv
    have hw := L.weightH_le x hv
    have hs : (PNorm.fin q hq).s = 2 := min_eq_right hq2.le
    rw [hs]
    change (L.weightH x v : ℝ) ≤ 16 * L.numBlocks *
      (lpNorm q (LatticeFamily.toReal (L.latticeH.target x - v)) / (⌈R₀⌉₊ : ℝ)) ^ (2 : ℝ)
    have hpm := sum_sq_le_card_rpow_mul hq2.le (LatticeFamily.toReal (L.latticeH.target x - v))
    rw [hcardR] at hpm
    simp only [LatticeFamily.toReal] at hpm hw ⊢
    exact radius_bound_gt_two hq2 ht1 hD1 (sum_abs_rpow_nonneg _ _) hw hpm

/-- Case `p = ∞`. -/
noncomputable def reduction_inf {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) :
    LatticeReduction L g PNorm.inf := by
  have hD1 : (1 : ℝ) ≤ L.numBlocks := by exact_mod_cast hD
  have ht1 : (1 : ℝ) ≤ (2 ^ L.padK : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have hcardR : (Fintype.card L.PadM : ℝ) = 2 * ((2 ^ L.padK : ℝ) * L.numBlocks) := by
    rw [L.card_padM]; push_cast; ring
  have hne : Nonempty L.PadM := by
    obtain ⟨b⟩ := Fintype.card_pos_iff.mp hD
    exact ⟨(Sum.inl b, 0)⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨L.latticeH, 1, le_rfl, Fintype.card_pos, L.two_mul_card_le_card_padM,
    L.card_padM_lt hg hD, p * 2 ^ L.padK, by positivity, L.latticeH_smul_mem, L.weightH, ?_, ?_,
    fun x hno v hv => L.lt_weightH hg hD hno hv⟩
  · -- YES
    intro x hx
    obtain ⟨v, hv, habs, -⟩ := L.latticeH_yes hx
    refine ⟨v, hv, ?_⟩
    change supNorm (LatticeFamily.toReal (L.latticeH.target x - v)) ≤ ((1 : ℕ) : ℝ)
    rw [Nat.cast_one]
    refine supNorm_le zero_le_one fun i => ?_
    simp only [LatticeFamily.toReal]
    rw [← Int.cast_abs]
    exact_mod_cast habs i
  · -- the weight bound
    intro x v hv
    have hw := L.weightH_le x hv
    change (L.weightH x v : ℝ) ≤ 16 * L.numBlocks *
      (supNorm (LatticeFamily.toReal (L.latticeH.target x - v)) / ((1 : ℕ) : ℝ)) ^ (2 : ℝ)
    have hsup := sum_sq_le_card_mul_supNorm_sq (LatticeFamily.toReal (L.latticeH.target x - v))
    rw [hcardR] at hsup
    simp only [LatticeFamily.toReal] at hsup hw ⊢
    exact radius_bound_inf (by positivity) (by linarith) hw hsup

end LinearSystemFamily

end Cases

/-- **Lemma 3.8** (the lattice reduction). Given a linear system family over `𝔽_p` with gap
`g < b` and at least one block, there is a `LatticeReduction`: a fixed full-rank lattice
`Λ ⊆ ℤ^M` with `2 n ≤ M < 4 n` (`n = |ι|`), an integer radius `1 ≤ R ≤ M`, targets, and a
residual weight such that

* YES instances have a lattice vector within `ℓ_p`-distance `R` of the target;
* every lattice vector `v` has residual weight `w ≤ 16 · D · (dist / R)^s`, and `w > g · D` on NO
  instances. -/
theorem exists_latticeReduction {p : ℕ} [Fact p.Prime] {X : Type}
    (L : LinearSystemFamily (ZMod p) X) {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    (pn : PNorm) : Nonempty (LatticeReduction L g pn) := by
  rcases pn with ⟨q, hq⟩ | _
  · rcases le_or_gt q 2 with hq2 | hq2
    · exact ⟨L.reduction_le_two hg hD hq hq2⟩
    · exact ⟨L.reduction_gt_two hg hD hq hq2⟩
  · exact ⟨L.reduction_inf hg hD⟩

end LatticePrepro
