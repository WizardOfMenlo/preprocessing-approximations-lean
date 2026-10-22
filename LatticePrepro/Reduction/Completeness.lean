import LatticePrepro.Basic.Finset
import LatticePrepro.Reduction.FixedSystem

/-!
# Completeness of the fixed-verifier system (Theorem 4.6, completeness)

For an accepting computation `z` on `x`, the *honest solution* consists of the product tables
`v_{i,j} = z_i z_j · ê_{α_S}` and the auxiliary tables `v^{(i)} = z_i · ê_{α_{i-1}}`, where
`α_i = ∑_{j ≤ i} z_j E_j` is the partial encoding of `z` (so `α_S = enc z` and
`α_{n+1} = θ_x`). It satisfies every equation of Construction 4.5, is binary, and has at most one
nonzero coordinate per block.
-/

namespace LatticePrepro

namespace FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

/-! ### Partial encodings -/

/-- The partial encoding `α_i = ∑_{j ≤ i} z_j • E_j`. -/
def partialEnc (z : Fin (V.S + 1) → ZMod p) (i : ℕ) : K :=
  ∑ j : Fin (V.S + 1), (if j.val ≤ i then z j else 0) • ε.E j

lemma partialEnc_top (z : Fin (V.S + 1) → ZMod p) : partialEnc V ε z V.S = ε.enc z := by
  unfold partialEnc EncodingTuple.enc
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ite_eq_left (Nat.le_of_lt_succ j.isLt)]

lemma partialEnc_succ (z : Fin (V.S + 1) → ZMod p) {i : ℕ} (hi : 1 ≤ i) (hiS : i ≤ V.S) :
    partialEnc V ε z i =
      partialEnc V ε z (i - 1) + z ⟨i, by omega⟩ • ε.E ⟨i, by omega⟩ := by
  unfold partialEnc
  have key : ∀ j : Fin (V.S + 1), (if j.val ≤ i then z j else 0) • ε.E j =
      (if j.val ≤ i - 1 then z j else 0) • ε.E j +
        (if j = ⟨i, by omega⟩ then z j • ε.E j else 0) := by
    intro j
    by_cases hj : j = ⟨i, by omega⟩
    · subst hj
      simp only [ite_true]
      rw [ite_eq_left le_rfl, ite_eq_right (by omega), zero_smul, zero_add]
    · rw [ite_eq_right hj, add_zero]
      have hj' : j.val ≠ i := fun h => hj (Fin.ext h)
      by_cases h : j.val ≤ i
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]

/-- For an assignment with prefix `(x, 1)`, the partial encoding up to `n + 1` is `θ_x`. -/
lemma partialEnc_prefix {x : Fin V.n → Bool} {z : Fin (V.S + 1) → ZMod p} (h0 : z 0 = 1)
    (hpre : V.HasPrefix x z) : partialEnc V ε z (V.n + 1) = V.instanceEnc ε x := by
  unfold partialEnc QuadraticVerifier.instanceEnc EncodingTuple.enc
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  by_cases hj : j.val ≤ V.n + 1
  · rw [ite_eq_left hj]
    by_cases hj0 : j.val = 0
    · rw [show j = 0 from Fin.ext hj0, h0, V.assignOf_zero]
    by_cases hjn : j.val ≤ V.n
    · rw [V.assignOf_apply_of_le x 0 hj0 hjn]
      have := hpre.1 ⟨j.val - 1, by omega⟩
      rw [show V.inputIdx ⟨j.val - 1, by omega⟩ = j from
        Fin.ext (by simp [QuadraticVerifier.inputIdx]; omega)] at this
      exact this
    · have hje : j.val = V.n + 1 := by omega
      rw [V.assignOf_apply_of_eq x 0 hje, show j = V.outputIdx from Fin.ext hje]
      exact hpre.2
  · rw [ite_eq_right hj, V.assignOf_apply_of_lt x 0 (by omega)]
    rfl

/-! ### The honest solution -/

/-- The tables of the honest solution. -/
noncomputable def honestTbl (z : Fin (V.S + 1) → ZMod p) : V.TblIdx → R.ι → ZMod p :=
  Sum.elim (fun T => (z T.1.1 * z T.1.2) • R.elemTable (partialEnc V ε z V.S))
    (fun i => z i.1 • R.elemTable (partialEnc V ε z (i.1.val - 1)))

/-- The honest solution. -/
noncomputable def honest (z : Fin (V.S + 1) → ZMod p) : Col V R → ZMod p :=
  fun c => honestTbl V R ε z c.1 c.2

lemma tbl_honest (z : Fin (V.S + 1) → ZMod p) (T : V.TblIdx) :
    tbl V R (honest V R ε z) T = honestTbl V R ε z T := rfl

/-- For a Boolean assignment, the product of the coordinates of the representative of `(i, j)`
is `z_i z_j`. -/
lemma rep_mul {z : Fin (V.S + 1) → ZMod p} (hz : V.IsBooleanAssignment z) (i j : Fin (V.S + 1)) :
    z (V.rep i j).1.1 * z (V.rep i j).1.2 = z i * z j := by
  obtain ⟨h0, hb⟩ := hz
  unfold QuadraticVerifier.rep
  split_ifs with h1 h2 h3
  · rfl
  · exact mul_comm _ _
  · have hij : i = j := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    subst hij
    subst h3
    rfl
  · have hij : i = j := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    subst hij
    simp only [h0, mul_one]
    rcases hb i with h | h <;> simp [h]

lemma momentMap_ptbl_honest {z : Fin (V.S + 1) → ZMod p} (hz : V.IsBooleanAssignment z)
    (i j : Fin (V.S + 1)) (k : R.Order) :
    R.momentMap k (ptbl V R (honest V R ε z) i j) =
      (z i * z j) • partialEnc V ε z V.S ^ (k : ℕ) := by
  simp only [ptbl, tbl_honest, honestTbl, Sum.elim_inl, map_smul, R.momentMap_elemTable,
    rep_mul V hz]

lemma momentMap_atbl_honest (z : Fin (V.S + 1) → ZMod p) (i : V.AuxIdx) (k : R.Order) :
    R.momentMap k (atbl V R (honest V R ε z) i) =
      z i.1 • partialEnc V ε z (i.1.val - 1) ^ (k : ℕ) := by
  simp only [atbl, tbl_honest, honestTbl, Sum.elim_inr, map_smul, R.momentMap_elemTable]

/-! ### Telescoping -/

omit [Fact (Nat.Prime p)] [Algebra (ZMod p) K] in
/-- Summing a telescoping difference over the auxiliary indices. -/
lemma sum_aux_telescope (f : ℕ → K) :
    ∑ i : V.AuxIdx, (f i.1.val - f (i.1.val - 1)) = f V.S - f (V.n + 1) := by
  classical
  have h1 : ∑ i : V.AuxIdx, (f i.1.val - f (i.1.val - 1)) =
      ∑ m ∈ Finset.Ico (V.n + 2) (V.S + 1), (f m - f (m - 1)) := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun i : Fin (V.S + 1) => V.n + 1 < i.val)
      (by simp) (fun i : Fin (V.S + 1) => f i.val - f (i.val - 1)), Finset.sum_filter,
      Fin.sum_univ_eq_sum_range (fun m => if V.n + 1 < m then f m - f (m - 1) else 0) (V.S + 1),
      ← Finset.sum_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h1, sum_Ico_telescope f (by have := V.n_succ_le; omega)]
  rfl

/-! ### The honest solution satisfies the equations -/

lemma honest_constraint (z : Fin (V.S + 1) → ZMod p) (T : V.TblIdx) :
    R.constraint (tbl V R (honest V R ε z) T) = 0 := by
  rw [tbl_honest]
  rcases T with T | i <;> simp [honestTbl, map_smul, R.constraint_elemTable]

lemma honest_encoding {z : Fin (V.S + 1) → ZMod p} (hz : V.IsBooleanAssignment z)
    (j : Fin (V.S + 1)) (k : Fin R.r) :
    R.momentMap (R.lowSucc k) (ptbl V R (honest V R ε z) 0 j) =
      ∑ i, ε.E i * R.momentMap (R.low k) (ptbl V R (honest V R ε z) i j) := by
  rw [momentMap_ptbl_honest V R ε hz 0 j]
  simp_rw [momentMap_ptbl_honest V R ε hz _ j]
  rw [hz.1, one_mul, MomentRepresentation.lowSucc_val, MomentRepresentation.low_val]
  set α := partialEnc V ε z V.S with hα
  have hαs : α = ∑ i, algebraMap (ZMod p) K (z i) * ε.E i := by
    rw [hα, partialEnc_top, EncodingTuple.enc]
    simp [Algebra.smul_def]
  calc z j • α ^ ((k : ℕ) + 1)
      = (∑ i, algebraMap (ZMod p) K (z i) * ε.E i) * (z j • α ^ (k : ℕ)) := by
        rw [← hαs, Algebra.smul_def, Algebra.smul_def]; ring
    _ = ∑ i, ε.E i * ((z i * z j) • α ^ (k : ℕ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Algebra.smul_def, map_mul]
        ring

lemma honest_gate {z : Fin (V.S + 1) → ZMod p} (hz : V.IsBooleanAssignment z)
    (hval : V.IsValid z) (b : Fin V.G) (k : Fin R.r) :
    ∑ i, ∑ j, V.coeff b i j • R.momentMap (R.low k) (ptbl V R (honest V R ε z) i j) = 0 := by
  simp_rw [momentMap_ptbl_honest V R ε hz _ _, smul_smul, ← Finset.sum_smul]
  have := hval b
  unfold QuadraticVerifier.gateEq at this
  rw [this, zero_smul]

lemma honest_translation {x : Fin V.n → Bool} {z : Fin (V.S + 1) → ZMod p}
    (hz : V.IsBooleanAssignment z) (hpre : V.HasPrefix x z) (k : R.Order) :
    transLhs V R ε (honest V R ε z) k = V.instanceEnc ε x ^ (k : ℕ) := by
  have hterm : ∀ i : V.AuxIdx, ∑ j : Fin k, ((k : ℕ).choose j : K) * ε.E i.1 ^ ((k : ℕ) - j) *
      R.momentMap (R.below k j) (atbl V R (honest V R ε z) i) =
      partialEnc V ε z i.1.val ^ (k : ℕ) - partialEnc V ε z (i.1.val - 1) ^ (k : ℕ) := by
    intro i
    have hi1 : 1 ≤ i.1.val := by have := i.2; omega
    have hiS : i.1.val ≤ V.S := Nat.le_of_lt_succ i.1.isLt
    have hstep := partialEnc_succ V ε z hi1 hiS
    have hfin : (⟨i.1.val, by omega⟩ : Fin (V.S + 1)) = i.1 := Fin.ext rfl
    rw [hfin] at hstep
    simp_rw [momentMap_atbl_honest V R ε z i, MomentRepresentation.below_val]
    rw [Fin.sum_univ_eq_sum_range (fun j => ((k : ℕ).choose j : K) * ε.E i.1 ^ ((k : ℕ) - j) *
      (z i.1 • partialEnc V ε z (i.1.val - 1) ^ j)) (k : ℕ)]
    set β := partialEnc V ε z (i.1.val - 1)
    rcases hz.2 i.1 with h | h
    · rw [hstep, h, zero_smul, add_zero, sub_self]
      simp
    · rw [hstep, h, one_smul]
      have hexp : (β + ε.E i.1) ^ (k : ℕ) =
          (∑ j ∈ Finset.range (k : ℕ), β ^ j * ε.E i.1 ^ ((k : ℕ) - j) * ((k : ℕ).choose j : K)) +
            β ^ (k : ℕ) := by
        rw [add_pow, Finset.sum_range_succ]
        simp
      rw [hexp, add_sub_cancel_right]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_smul]
      ring
  rw [transLhs, momentMap_ptbl_honest V R ε hz 0 0, Finset.sum_congr rfl fun i _ => hterm i,
    sum_aux_telescope V (fun m => partialEnc V ε z m ^ (k : ℕ)), hz.1, one_mul, one_smul,
    sub_sub_cancel, partialEnc_prefix V ε hz.1 hpre]

/-- The honest solution satisfies all equations of Construction 4.5. -/
theorem honest_solves {x : Fin V.n → Bool} {z : Fin (V.S + 1) → ZMod p}
    (hz : V.IsBooleanAssignment z) (hval : V.IsValid z) (hpre : V.HasPrefix x z) :
    Solves V R ε x (honest V R ε z) where
  constraint := honest_constraint V R ε z
  encoding := fun j k => sub_eq_zero.mpr (honest_encoding V R ε hz j k)
  gate := fun b k => honest_gate V R ε hz hval b k
  translation := fun k => honest_translation V R ε hz hpre k

/-! ### Binary entries and block sparsity -/

lemma binary_mul {a b : ZMod p} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a * b = 0 ∨ a * b = 1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

lemma honest_binary {z : Fin (V.S + 1) → ZMod p} (hz : V.IsBooleanAssignment z) :
    IsBinary (honest V R ε z) := by
  rintro ⟨T | i, c⟩
  · exact binary_mul (binary_mul (hz.2 _) (hz.2 _)) (R.elemTable_binary _ c)
  · exact binary_mul (hz.2 _) (R.elemTable_binary _ c)

/-- The block support of a column block is the block support of the corresponding table. -/
lemma card_blockSupport_blk (v : Col V R → ZMod p) (T : V.TblIdx) (b : R.β) :
    (blockSupport (blk V R) v (T, b)).card = (blockSupport R.blk (tbl V R v T) b).card := by
  refine Finset.card_bij (fun c _ => c.2) ?_ ?_ ?_
  · rintro ⟨T', i⟩ hc
    rw [blockSupport, Finset.mem_filter] at hc ⊢
    obtain ⟨-, hblk, hne⟩ := hc
    simp only [blk, Prod.mk.injEq] at hblk
    exact ⟨Finset.mem_univ _, hblk.2, by rw [tbl, ← hblk.1]; exact hne⟩
  · rintro ⟨T₁, i₁⟩ hc₁ ⟨T₂, i₂⟩ hc₂ h
    rw [blockSupport, Finset.mem_filter] at hc₁ hc₂
    simp only [blk, Prod.mk.injEq] at hc₁ hc₂
    simp only at h
    rw [h, hc₁.2.1.1, hc₂.2.1.1]
  · intro i hi
    rw [blockSupport, Finset.mem_filter] at hi
    refine ⟨(T, i), ?_, rfl⟩
    rw [blockSupport, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [blk, hi.2.1], hi.2.2⟩

lemma honest_atMostOnePerBlock (z : Fin (V.S + 1) → ZMod p) :
    AtMostOnePerBlock (blk V R) (honest V R ε z) := by
  rintro ⟨T, b⟩
  rw [card_blockSupport_blk, tbl_honest]
  rcases T with T | i
  · exact ((R.elemTable_onePerBlock _).atMostOne.smul R.blk (z T.1.1 * z T.1.2)) b
  · exact ((R.elemTable_onePerBlock _).atMostOne.smul R.blk (z i.1)) b

/-- **Completeness** (Theorem 4.6). -/
theorem complete {x : Fin V.n → Bool} (hx : x ∈ V.Language) : (fixedSystem V R ε).IsYes x := by
  obtain ⟨z, hz, hval, hpre⟩ := hx
  exact ⟨honest V R ε z, (isSolution_iff V R ε x _).mpr (honest_solves V R ε hz hval hpre),
    honest_binary V R ε hz, honest_atMostOnePerBlock V R ε z⟩

end FixedSystem

end LatticePrepro
