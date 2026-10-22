import LatticePrepro.Reduction.Completeness

/-!
# Soundness of the fixed-verifier system (Theorem 4.6, soundness)

For a solution `v` of weight below the threshold `r · D / 2`, every table represents a
coefficient function on `Ω`, and these functions have fewer than `r` support points in total.
The encoding, gate and translation identities then hold pointwise (by the Vandermonde
identification lemma), the main function is supported on encodings of valid assignments
(Lemma 4.8), and summing the translation identity over the coset of assignments with prefix
`(x, 1)` exhibits an accepting computation on `x`.

The final results `mem_language_of_solves`, `sound` and `isGapReduction` live at the end of this
file.
-/

namespace LatticePrepro

open Finsupp

section Aux

variable {Ω : Type} [Field Ω]

/-- Multiplication of a coefficient function by the variable: `α ↦ α · h α`. -/
noncomputable def mulVar (h : Ω →₀ Ω) : Ω →₀ Ω :=
  Finsupp.onFinset h.support (fun α => α * h α) fun α hα => by
    rw [Finsupp.mem_support_iff]
    intro h0
    exact hα (by rw [h0, mul_zero])

@[simp] lemma mulVar_apply (h : Ω →₀ Ω) (α : Ω) : mulVar h α = α * h α := rfl

lemma support_mulVar_subset (h : Ω →₀ Ω) : (mulVar h).support ⊆ h.support :=
  Finsupp.support_onFinset_subset

lemma moment_mulVar (h : Ω →₀ Ω) (k : ℕ) : moment (mulVar h) k = moment h (k + 1) := by
  rw [moment_eq_sum_of_subset _ _ (support_mulVar_subset h), moment_eq_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mulVar_apply, smul_eq_mul, smul_eq_mul, pow_succ]
  ring

end Aux

namespace FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

lemma algebraMap_smul_eq (c : ZMod p) (y : K) :
    algebraMap K Ω (c • y) = c • algebraMap K Ω y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

/-! ### Lemma 4.8: recovering an assignment at a support point -/

/-- A vanishing `𝔽_p`-combination of the images of the `E_i` in `Ω` has zero coefficients
(except possibly at the constant index `0`). -/
lemma coeff_eq_zero_of_sum_smul_algebraMap {c : Fin (V.S + 1) → ZMod p}
    (h : ∑ i, c i • algebraMap K Ω (ε.E i) = 0) (i : Fin (V.S + 1)) (hi : i ≠ 0) : c i = 0 := by
  have h' : ∑ i, c i • ε.E i = 0 := by
    apply (algebraMap K Ω).injective
    rw [map_sum, map_zero, ← h]
    exact Finset.sum_congr rfl fun i _ => algebraMap_smul_eq _ _
  exact ε.eq_zero_of_sum_smul_eq_zero h' i hi

/-- **Lemma 4.8** (pointwise form). Values `Fv i j ∈ 𝔽_p` at a point `α` that are symmetric,
satisfy `Fv i i = Fv i 0`, the encoding identities and the gate identities, with `Fv 0 0 ≠ 0`,
come from a Boolean valid assignment `z` with `enc z = α`. -/
theorem recover {Fv : Fin (V.S + 1) → Fin (V.S + 1) → ZMod p}
    (hsymm : ∀ i j, Fv i j = Fv j i) (hdiag : ∀ i, Fv i i = Fv i 0) {α : Ω}
    (henc : ∀ j, α * algebraMap (ZMod p) Ω (Fv 0 j) =
      ∑ i, algebraMap K Ω (ε.E i) * algebraMap (ZMod p) Ω (Fv i j))
    (hgate : ∀ b, ∑ i, ∑ j, V.coeff b i j * Fv i j = 0) (hne : Fv 0 0 ≠ 0) :
    ∃ z : Fin (V.S + 1) → ZMod p, V.IsBooleanAssignment z ∧ V.IsValid z ∧
      algebraMap K Ω (ε.enc z) = α := by
  set a := Fv 0 0 with ha
  let z : Fin (V.S + 1) → ZMod p := fun i => Fv i 0 / a
  have hz0 : z 0 = 1 := div_self hne
  have hFi0 : ∀ i, Fv i 0 = a * z i := fun i => by
    simp only [z]
    rw [mul_div_cancel₀ _ hne]
  have ha' : algebraMap (ZMod p) Ω a ≠ 0 := (map_ne_zero _).mpr hne
  -- the point is the encoding of `z`
  have hα : α = algebraMap K Ω (ε.enc z) := by
    have h0 := henc 0
    rw [EncodingTuple.enc, map_sum]
    apply mul_right_cancel₀ ha'
    rw [h0, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFi0 i, map_mul, algebraMap_smul_eq, Algebra.smul_def]
    ring
  -- product structure
  have hprod : ∀ i j, Fv i j = a * (z i * z j) := by
    intro i j
    by_cases hi : i = 0
    · subst hi
      rw [hsymm 0 j, hFi0 j, hz0, one_mul]
    · have hj := henc j
      rw [hα, hsymm 0 j, hFi0 j] at hj
      have hl : algebraMap K Ω (ε.enc z) * algebraMap (ZMod p) Ω (a * z j) =
          ∑ i, (z i * (a * z j)) • algebraMap K Ω (ε.E i) := by
        rw [EncodingTuple.enc, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
        ring
      rw [hl] at hj
      have hcomb : ∑ i, (z i * (a * z j) - Fv i j) • algebraMap K Ω (ε.E i) = 0 := by
        rw [Finset.sum_congr rfl fun i _ => sub_smul _ _ _, Finset.sum_sub_distrib, hj,
          sub_eq_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def]
        ring
      have := coeff_eq_zero_of_sum_smul_algebraMap V ε hcomb i hi
      rw [sub_eq_zero] at this
      rw [← this]
      ring
  -- Boolean coordinates
  have hbool : ∀ i, z i = 0 ∨ z i = 1 := by
    intro i
    have h1 := hdiag i
    rw [hprod i i, hprod i 0, hz0, mul_one] at h1
    have h2 : z i * z i = z i := mul_left_cancel₀ hne h1
    have h3 : z i * (z i - 1) = 0 := by rw [mul_sub, mul_one, h2, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  -- validity
  have hvalid : V.IsValid z := by
    intro b
    have h := hgate b
    simp_rw [hprod] at h
    unfold QuadraticVerifier.gateEq
    apply mul_left_cancel₀ hne
    rw [mul_zero, Finset.mul_sum, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  exact ⟨z, ⟨hz0, hbool⟩, hvalid, hα.symm⟩

/-! ### Represented functions and their supports -/

open Classical in
/-- The union of the supports of the represented functions of all tables. -/
noncomputable def suppUnion (f : V.TblIdx → Ω →₀ ZMod p) : Finset Ω :=
  Finset.univ.biUnion fun T => (f T).support

omit [Field Ω] [Algebra (ZMod p) Ω] in
lemma mem_suppUnion {f : V.TblIdx → Ω →₀ ZMod p} {T : V.TblIdx} {α : Ω} (h : f T α ≠ 0) :
    α ∈ suppUnion V f := by
  classical
  unfold suppUnion
  exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩

omit [Field Ω] [Algebra (ZMod p) Ω] in
lemma eq_zero_of_notMem_suppUnion {f : V.TblIdx → Ω →₀ ZMod p} {α : Ω}
    (h : α ∉ suppUnion V f) (T : V.TblIdx) : f T α = 0 :=
  by_contra fun h' => h (mem_suppUnion V h')

omit [Field Ω] [Algebra (ZMod p) Ω] in
lemma card_suppUnion_le (f : V.TblIdx → Ω →₀ ZMod p) :
    (suppUnion V f).card ≤ ∑ T, (f T).support.card := by
  classical
  unfold suppUnion
  exact Finset.card_biUnion_le

lemma hammingNorm_tbl_le (v : Col V R → ZMod p) (T : V.TblIdx) :
    hammingNorm (tbl V R v T) ≤ hammingNorm v := by
  rw [hammingNorm_eq_sum_tbl]
  exact Finset.single_le_sum (f := fun T => hammingNorm (tbl V R v T)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ T)

section Identities

variable {x : Fin V.n → Bool} {v : Col V R → ZMod p} (hv : Solves V R ε x v)
  (f : V.TblIdx → Ω →₀ ZMod p)
  (hf : ∀ T (k : R.Order), algebraMap K Ω (R.momentMap k (tbl V R v T)) = moment (f T) k)
  (hN : ∑ T, (f T).support.card < R.r)

include hv hf hN

/-- The encoding identity holds pointwise (paper, §4.4). -/
theorem encoding_pointwise (j : Fin (V.S + 1)) (α : Ω) :
    α * algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 j)) α) =
      ∑ i, algebraMap K Ω (ε.E i) * algebraMap (ZMod p) Ω (f (Sum.inl (V.rep i j)) α) := by
  set g : Ω →₀ Ω := mulVar (extendScalars (f (Sum.inl (V.rep 0 j)))) -
    ∑ i, algebraMap K Ω (ε.E i) • extendScalars (f (Sum.inl (V.rep i j))) with hg
  have hgapp : ∀ β, g β = β * algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 j)) β) -
      ∑ i, algebraMap K Ω (ε.E i) * algebraMap (ZMod p) Ω (f (Sum.inl (V.rep i j)) β) := by
    intro β
    simp [hg, Algebra.smul_def]
  have hsupp : g.support ⊆ suppUnion V f := by
    intro β hβ
    rw [Finsupp.mem_support_iff] at hβ
    by_contra hβU
    apply hβ
    rw [hgapp]
    simp [eq_zero_of_notMem_suppUnion V hβU]
  have hmom : ∀ k < R.r, moment g k = 0 := by
    intro k hk
    have : moment g k = algebraMap K Ω (encLhs V R ε v j ⟨k, hk⟩) := by
      rw [encLhs, map_sub, map_sum, hg, moment_sub, moment_finset_sum, moment_mulVar,
        moment_extendScalars]
      unfold ptbl
      rw [hf _ (R.lowSucc ⟨k, hk⟩), MomentRepresentation.lowSucc_val]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [moment_smul, moment_extendScalars, smul_eq_mul, map_mul, hf _ (R.low ⟨k, hk⟩),
        MomentRepresentation.low_val]
    rw [this, hv.encoding j ⟨k, hk⟩, map_zero]
  have hg0 : g = 0 := eq_zero_of_moment_eq_zero g
    ((Finset.card_le_card hsupp).trans ((card_suppUnion_le V f).trans hN.le)) hmom
  have h0 : g α = 0 := by rw [hg0]; rfl
  rw [hgapp] at h0
  exact sub_eq_zero.mp h0

/-- The gate identities hold pointwise (paper, §4.4). -/
theorem gate_pointwise (b : Fin V.G) (α : Ω) :
    ∑ i, ∑ j, V.coeff b i j * f (Sum.inl (V.rep i j)) α = 0 := by
  set g : Ω →₀ Ω := ∑ i, ∑ j,
    algebraMap (ZMod p) Ω (V.coeff b i j) • extendScalars (f (Sum.inl (V.rep i j))) with hg
  have hgapp : ∀ β, g β =
      algebraMap (ZMod p) Ω (∑ i, ∑ j, V.coeff b i j * f (Sum.inl (V.rep i j)) β) := by
    intro β
    simp [hg, Algebra.smul_def]
  have hsupp : g.support ⊆ suppUnion V f := by
    intro β hβ
    rw [Finsupp.mem_support_iff] at hβ
    by_contra hβU
    apply hβ
    rw [hgapp]
    simp [eq_zero_of_notMem_suppUnion V hβU]
  have hmom : ∀ k < R.r, moment g k = 0 := by
    intro k hk
    have : moment g k = algebraMap K Ω (gateLhs V R v b ⟨k, hk⟩) := by
      rw [gateLhs, map_sum, hg, moment_finset_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, moment_finset_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [moment_smul, moment_extendScalars, smul_eq_mul, algebraMap_smul_eq, Algebra.smul_def]
      unfold ptbl
      rw [hf _ (R.low ⟨k, hk⟩), MomentRepresentation.low_val]
    rw [this, hv.gate b ⟨k, hk⟩, map_zero]
  have hg0 : g = 0 := eq_zero_of_moment_eq_zero g
    ((Finset.card_le_card hsupp).trans ((card_suppUnion_le V f).trans hN.le)) hmom
  have h0 : g α = 0 := by rw [hg0]; rfl
  rw [hgapp] at h0
  exact (map_eq_zero_iff _ (algebraMap (ZMod p) Ω).injective).mp h0

/-- The translation identity holds pointwise (paper, §4.4). -/
theorem translation_pointwise (α : Ω) :
    algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) α) -
      ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (α - algebraMap K Ω (ε.E i.1))) -
        algebraMap (ZMod p) Ω (f (Sum.inr i) α)) -
      Finsupp.single (algebraMap K Ω (V.instanceEnc ε x)) (1 : Ω) α = 0 := by
  classical
  set g : Ω →₀ Ω := extendScalars (f (Sum.inl (V.rep 0 0))) -
    ∑ i : V.AuxIdx, (translate (algebraMap K Ω (ε.E i.1)) (extendScalars (f (Sum.inr i))) -
      extendScalars (f (Sum.inr i))) - Finsupp.single (algebraMap K Ω (V.instanceEnc ε x)) 1
    with hg
  have hgapp : ∀ β, g β = algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) β) -
      ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (β - algebraMap K Ω (ε.E i.1))) -
        algebraMap (ZMod p) Ω (f (Sum.inr i) β)) -
      Finsupp.single (algebraMap K Ω (V.instanceEnc ε x)) (1 : Ω) β := by
    intro β
    simp [hg, translate_apply]
  -- support bound
  have hsum_aux : ∑ i : V.AuxIdx, (f (Sum.inr i)).support.card ≤ ∑ T, (f T).support.card := by
    rw [Fintype.sum_sum_type]
    exact Nat.le_add_left _ _
  set W : Finset Ω := suppUnion V f ∪
    (Finset.univ.biUnion fun i : V.AuxIdx =>
      (f (Sum.inr i)).support.map (addRightEmbedding (algebraMap K Ω (ε.E i.1))))
    ∪ {algebraMap K Ω (V.instanceEnc ε x)} with hW
  have hsupp : g.support ⊆ W := by
    intro β hβ
    rw [Finsupp.mem_support_iff] at hβ
    by_contra hβW
    apply hβ
    rw [hW, Finset.mem_union, Finset.mem_union, not_or, not_or] at hβW
    obtain ⟨⟨hβU, hβsh⟩, hβθ⟩ := hβW
    rw [Finset.mem_singleton] at hβθ
    have h1 : ∀ i : V.AuxIdx, f (Sum.inr i) (β - algebraMap K Ω (ε.E i.1)) = 0 := by
      intro i
      by_contra hne
      apply hβsh
      rw [Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, Finset.mem_map.mpr
        ⟨β - algebraMap K Ω (ε.E i.1), Finsupp.mem_support_iff.mpr hne, by simp⟩⟩
    rw [hgapp, eq_zero_of_notMem_suppUnion V hβU, map_zero, zero_sub,
      Finsupp.single_apply, ite_eq_right (Ne.symm hβθ), sub_zero, neg_eq_zero]
    exact Finset.sum_eq_zero fun i _ => by
      rw [h1 i, eq_zero_of_notMem_suppUnion V hβU, map_zero, sub_self]
  have hcardW : W.card ≤ 2 * R.r - 1 := by
    have hr := R.two_le_r
    calc W.card ≤ ((suppUnion V f ∪ (Finset.univ.biUnion fun i : V.AuxIdx =>
          (f (Sum.inr i)).support.map (addRightEmbedding (algebraMap K Ω (ε.E i.1))))).card +
          ({algebraMap K Ω (V.instanceEnc ε x)} : Finset Ω).card) :=
          Finset.card_union_le _ _
      _ ≤ (suppUnion V f).card + (Finset.univ.biUnion fun i : V.AuxIdx =>
          (f (Sum.inr i)).support.map (addRightEmbedding (algebraMap K Ω (ε.E i.1)))).card + 1 := by
          rw [Finset.card_singleton]
          exact Nat.add_le_add_right (Finset.card_union_le _ _) 1
      _ ≤ (∑ T, (f T).support.card) + (∑ i : V.AuxIdx, (f (Sum.inr i)).support.card) + 1 := by
          refine Nat.add_le_add_right (Nat.add_le_add (card_suppUnion_le V f) ?_) 1
          refine Finset.card_biUnion_le.trans ?_
          simp [Finset.card_map]
      _ ≤ (∑ T, (f T).support.card) + (∑ T, (f T).support.card) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_left hsum_aux _) 1
      _ ≤ 2 * R.r - 1 := by omega
  -- moments
  have hmom : ∀ k < 2 * R.r - 1, moment g k = 0 := by
    intro k hk
    have : moment g k = algebraMap K Ω (transLhs V R ε v ⟨k, hk⟩ - V.instanceEnc ε x ^ k) := by
      rw [transLhs, map_sub, map_sub, map_sum, map_pow, hg, moment_sub, moment_sub,
        moment_finset_sum, moment_extendScalars, moment_single, one_smul]
      unfold ptbl atbl
      rw [hf _ ⟨k, hk⟩]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [moment_translate_sub, map_sum, ← Fin.sum_univ_eq_sum_range (fun j =>
        (k.choose j : Ω) * algebraMap K Ω (ε.E i.1) ^ (k - j) *
          moment (extendScalars (f (Sum.inr i))) j) k]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [moment_extendScalars, map_mul, map_mul, map_pow, map_natCast,
        hf _ (R.below ⟨k, hk⟩ j), MomentRepresentation.below_val]
    rw [this, hv.translation ⟨k, hk⟩, sub_self, map_zero]
  have hg0 : g = 0 := eq_zero_of_moment_eq_zero g
    ((Finset.card_le_card hsupp).trans hcardW) hmom
  have h0 : g α = 0 := by rw [hg0]; rfl
  rw [hgapp] at h0
  exact h0

end Identities

/-! ### Soundness -/

/-- **Soundness, weight form** (Theorem 4.6): a solution of weight below the threshold `r · D / 2`
certifies membership in the language. -/
theorem mem_language_of_solves {x : Fin V.n → Bool} {v : Col V R → ZMod p}
    (hv : Solves V R ε x v) (hw : 2 * hammingNorm v < R.r * R.numBlocks) : x ∈ V.Language := by
  classical
  -- (1) represented functions
  have htbl : ∀ T, 2 * hammingNorm (tbl V R v T) < R.r * R.numBlocks := fun T =>
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 (hammingNorm_tbl_le V R v T)) hw
  choose f hf using fun T => R.sound (tbl V R v T) (hv.constraint T) (htbl T)
  have hf' : ∀ T (k : R.Order),
      algebraMap K Ω (R.momentMap k (tbl V R v T)) = moment (f T) k := fun T => (hf T).1
  have hN : ∑ T, (f T).support.card < R.r := by
    have h1 : R.numBlocks * ∑ T, (f T).support.card ≤ 2 * hammingNorm v := by
      rw [Finset.mul_sum, hammingNorm_eq_sum_tbl, Finset.mul_sum]
      exact Finset.sum_le_sum fun T _ => (hf T).2
    have h2 : R.numBlocks * ∑ T, (f T).support.card < R.numBlocks * R.r :=
      calc _ ≤ 2 * hammingNorm v := h1
        _ < R.r * R.numBlocks := hw
        _ = R.numBlocks * R.r := mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_left h2
  -- (5) the coset sum
  set θ : Ω := algebraMap K Ω (V.instanceEnc ε x) with hθ
  set c : V.AuxIdx → Ω := fun i => algebraMap K Ω (ε.E i.1) with hc
  let pt : (V.AuxIdx → ZMod p) → Ω := fun u => algebraMap K Ω (ε.enc (V.assignOf x u))
  have hpt : ∀ u, pt u = θ + ∑ i, u i • c i := by
    intro u
    simp only [pt, V.enc_assignOf ε x u, map_add, map_sum, algebraMap_smul_eq, hθ, hc]
  have hpt0 : pt 0 = θ := by
    simp only [pt]
    rfl
  have hpt_sub : ∀ u (i : V.AuxIdx), pt (u - Pi.single i 1) = pt u - c i := by
    intro u i
    rw [hpt, hpt]
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul,
      zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hpt_eq : ∀ u, pt u = θ ↔ u = 0 := by
    intro u
    constructor
    · intro h
      have h1 : ε.enc (V.assignOf x u) = ε.enc (V.assignOf x 0) :=
        (algebraMap K Ω).injective (by rw [← hpt0] at h; exact h)
      have h2 : V.assignOf x u = V.assignOf x 0 :=
        ε.enc_injective (by rw [V.assignOf_zero, V.assignOf_zero]) h1
      funext i
      have := congrFun h2 i.1
      rw [V.assignOf_aux, V.assignOf_aux] at this
      exact this
    · rintro rfl; exact hpt0
  -- sum the pointwise translation identity over the coset
  have hT : ∀ u, algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) (pt u)) -
      ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (pt u - c i)) -
        algebraMap (ZMod p) Ω (f (Sum.inr i) (pt u))) -
      Finsupp.single θ (1 : Ω) (pt u) = 0 :=
    fun u => translation_pointwise V R ε hv f hf' hN (pt u)
  have hsum0 := Finset.sum_eq_zero (s := Finset.univ) fun u _ => hT u
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum0
  have hmid : ∑ u, ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (pt u - c i)) -
      algebraMap (ZMod p) Ω (f (Sum.inr i) (pt u))) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact Fintype.sum_equiv (Equiv.subRight (Pi.single i 1)) _ _ fun u => by
      simp [hpt_sub]
  have hlast : ∑ u, Finsupp.single θ (1 : Ω) (pt u) = 1 := by
    rw [Finset.sum_eq_single (0 : V.AuxIdx → ZMod p)]
    · rw [hpt0, Finsupp.single_eq_same]
    · intro u _ hu
      have : pt u ≠ θ := fun h => hu ((hpt_eq u).mp h)
      rw [Finsupp.single_apply, ite_eq_right (Ne.symm this)]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hmid, hlast, sub_zero, sub_eq_zero] at hsum0
  obtain ⟨u, hu⟩ : ∃ u, f (Sum.inl (V.rep 0 0)) (pt u) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have : ∑ u, algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) (pt u)) = 0 :=
      Finset.sum_eq_zero fun u _ => by rw [h u, map_zero]
    rw [this] at hsum0
    exact zero_ne_one hsum0
  -- (4) recover an accepting computation at the support point
  obtain ⟨z, hzb, hzv, hzenc⟩ := recover V ε (Fv := fun i j => f (Sum.inl (V.rep i j)) (pt u))
    (fun i j => by rw [V.rep_comm]) (fun i => by rw [V.rep_diag])
    (fun j => encoding_pointwise V R ε hv f hf' hN j (pt u))
    (fun b => gate_pointwise V R ε hv f hf' hN b (pt u)) hu
  have hz : z = V.assignOf x u := by
    apply ε.enc_injective (by rw [hzb.1, V.assignOf_zero])
    exact (algebraMap K Ω).injective hzenc
  exact ⟨z, hzb, hzv, hz ▸ V.assignOf_hasPrefix x u⟩

/-- **Soundness** (Theorem 4.6). -/
theorem sound {g : ℕ} (hg : 2 * g * Fintype.card V.TblIdx < R.r) {x : Fin V.n → Bool}
    (hx : x ∉ V.Language) : (fixedSystem V R ε).IsNo g x := by
  intro v hv
  have hv : Solves V R ε x v := (isSolution_iff V R ε x v).mp hv
  by_contra hcon
  rw [not_lt] at hcon
  apply hx
  apply mem_language_of_solves V R ε hv
  rw [numBlocks_eq] at hcon
  have hD : 0 < R.numBlocks := R.numBlocks_pos
  calc 2 * hammingNorm v ≤ 2 * (g * (Fintype.card V.TblIdx * R.numBlocks)) := by
        exact Nat.mul_le_mul_left 2 hcon
    _ = (2 * g * Fintype.card V.TblIdx) * R.numBlocks := by ring
    _ < R.r * R.numBlocks := Nat.mul_lt_mul_of_pos_right hg hD

/-- **Theorem 4.6**: the fixed-verifier system is a gap reduction with gap `g`
whenever `2 · g · N < r`. -/
theorem isGapReduction {g : ℕ} (hg : 2 * g * Fintype.card V.TblIdx < R.r) :
    (fixedSystem V R ε).IsGapReduction V.Language g :=
  ⟨fun _ hx => complete V R ε hx, fun _ hx => sound V R ε hg hx⟩

end FixedSystem

end LatticePrepro
