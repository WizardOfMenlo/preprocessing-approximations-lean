import LatticePrepro.Reduction.LinearSystem

/-!
# From linear systems to codes (Lemma 3.7, Appendix B.1)

Given a linear system family `A · v = b_x` over `𝔽_p` with columns `ι`, we build a fixed code
`𝒞 = ker A × {0} ⊆ 𝔽_p^{ι ⊕ ι}` and targets `y_x`: a solution `(v_0, 0)` of the system when one
exists, and `(0, 1)` otherwise. Then `y_x - 𝒞` is the set of solutions (padded by zeros), so

* YES instances have a binary vector `e` with `y_x - e ∈ 𝒞`, at most one nonzero entry per block
  and weight `≤ D`;
* NO instances have `dist(y_x, 𝒞) > g · D`.

The code is then extended by scalars to any finite field `F ⊇ 𝔽_p`, which preserves distances
to targets over `𝔽_p`.
-/

namespace LatticePrepro

/-- A fixed linear code with a target for every instance. -/
structure CodeFamily (F : Type) [Field F] (X : Type) where
  /-- Coordinates. -/
  M : Type
  [fintypeM : Fintype M]
  [decEqM : DecidableEq M]
  /-- The code. -/
  code : Submodule F (M → F)
  /-- The target for instance `x`. -/
  target : X → (M → F)

namespace CodeFamily

variable {F : Type} [Field F] {X : Type}

attribute [instance] fintypeM decEqM

/-- Hamming distance from a word to a code (Definition 3.1). -/
noncomputable def codeDist [DecidableEq F] {M : Type} [Fintype M] (y : M → F)
    (C : Submodule F (M → F)) : ℕ :=
  sInf {d | ∃ c ∈ C, hammingDist y c = d}

lemma codeDist_le [DecidableEq F] {M : Type} [Fintype M] (y : M → F) (C : Submodule F (M → F))
    {c : M → F} (hc : c ∈ C) : codeDist y C ≤ hammingDist y c :=
  Nat.sInf_le ⟨c, hc, rfl⟩

lemma exists_codeDist_eq [DecidableEq F] {M : Type} [Fintype M] (y : M → F)
    (C : Submodule F (M → F)) : ∃ c ∈ C, hammingDist y c = codeDist y C := by
  have hne : {d | ∃ c ∈ C, hammingDist y c = d}.Nonempty := ⟨hammingDist y 0, 0, C.zero_mem, rfl⟩
  exact Nat.sInf_mem hne

lemma lt_codeDist_of_forall [DecidableEq F] {M : Type} [Fintype M] (y : M → F)
    (C : Submodule F (M → F)) {d : ℕ} (h : ∀ c ∈ C, d < hammingDist y c) : d < codeDist y C := by
  obtain ⟨c, hc, hd⟩ := exists_codeDist_eq y C
  rw [← hd]; exact h c hc

end CodeFamily

section OfSystem

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

/-- The code `ker A × {0}` of Lemma 3.7. -/
def LinearSystemFamily.code : Submodule (ZMod p) (L.ι ⊕ L.ι → ZMod p) :=
  LinearMap.ker ((L.A.comp (LinearMap.funLeft (ZMod p) (ZMod p) Sum.inl)).prod
    (LinearMap.funLeft (ZMod p) (ZMod p) Sum.inr))

open Classical in
/-- The target `y_x` of Lemma 3.7. -/
noncomputable def LinearSystemFamily.codeTarget (x : X) : L.ι ⊕ L.ι → ZMod p :=
  if h : ∃ v, L.IsSolution x v then Sum.elim h.choose 0 else Sum.elim 0 1

/-- The block of a code coordinate. -/
def LinearSystemFamily.codeBlk : L.ι ⊕ L.ι → L.β ⊕ L.β := Sum.map L.blk L.blk

/-- The code family of Lemma 3.7 over the prime field. -/
noncomputable def LinearSystemFamily.toCodeFamily : CodeFamily (ZMod p) X where
  M := L.ι ⊕ L.ι
  code := L.code
  target := L.codeTarget

/-- Membership in the code `ker A × {0}`. -/
lemma LinearSystemFamily.mem_code_iff (w : L.ι ⊕ L.ι → ZMod p) :
    w ∈ L.code ↔ L.A (w ∘ Sum.inl) = 0 ∧ ∀ i, w (Sum.inr i) = 0 := by
  simp [LinearSystemFamily.code, LinearMap.mem_ker, funext_iff]
  exact fun _ => Iff.rfl

lemma LinearSystemFamily.codeTarget_of_exists {x : X} (h : ∃ v, L.IsSolution x v) :
    L.codeTarget x = Sum.elim h.choose 0 := by
  simp [LinearSystemFamily.codeTarget, h]

lemma LinearSystemFamily.codeTarget_of_not_exists {x : X} (h : ¬ ∃ v, L.IsSolution x v) :
    L.codeTarget x = Sum.elim (0 : L.ι → ZMod p) (1 : L.ι → ZMod p) := by
  simp [LinearSystemFamily.codeTarget, h]

/-- The Hamming weight of a vector on a sum type is the sum of the weights of its halves. -/
lemma hammingNorm_sum_elim {α β γ : Type*} [Fintype α] [Fintype β] [Zero γ] [DecidableEq γ]
    (a : α → γ) (b : β → γ) : hammingNorm (Sum.elim a b) = hammingNorm a + hammingNorm b := by
  simp only [hammingNorm, Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

/-- The Hamming distance of vectors on a sum type is the sum of the distances of their halves. -/
lemma hammingDist_sum_elim {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (a c : α → γ) (b d : β → γ) :
    hammingDist (Sum.elim a b) (Sum.elim c d) = hammingDist a c + hammingDist b d := by
  simp only [hammingDist, Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

lemma LinearSystemFamily.card_blockSupport_codeBlk_inl (v w : L.ι → ZMod p) (t : L.β) :
    (blockSupport L.codeBlk (Sum.elim v w) (Sum.inl t)).card = (blockSupport L.blk v t).card := by
  unfold blockSupport
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
    Sum.inl.injEq, reduceCtorEq, false_and, ite_false, Finset.sum_const_zero, add_zero]

lemma LinearSystemFamily.card_blockSupport_codeBlk_inr (v w : L.ι → ZMod p) (t : L.β) :
    (blockSupport L.codeBlk (Sum.elim v w) (Sum.inr t)).card = (blockSupport L.blk w t).card := by
  unfold blockSupport
  rw [Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr,
    Sum.inr.injEq, reduceCtorEq, false_and, ite_false, Finset.sum_const_zero, zero_add]

lemma LinearSystemFamily.card_codeBlk_fiber (s : L.β ⊕ L.β) :
    (Finset.univ.filter fun i => L.codeBlk i = s).card = L.blockSize := by
  rcases s with t | t
  · rw [← L.card_fiber t, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.inl.injEq, reduceCtorEq,
      ite_false, Finset.sum_const_zero, add_zero]
  · rw [← L.card_fiber t, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.inr.injEq, reduceCtorEq,
      ite_false, Finset.sum_const_zero, zero_add]

/-- YES instances (equation (B.1)): a binary block-sparse error vector of weight `≤ D`. -/
theorem LinearSystemFamily.code_yes {x : X} (hx : L.IsYes x) :
    ∃ e : L.ι ⊕ L.ι → ZMod p, IsBinary e ∧ AtMostOnePerBlock L.codeBlk e ∧
      hammingNorm e ≤ L.numBlocks ∧ L.codeTarget x - e ∈ L.code := by
  obtain ⟨v, hv, hb, ho⟩ := hx
  have hex : ∃ v, L.IsSolution x v := ⟨v, hv⟩
  refine ⟨Sum.elim v 0, ?_, ?_, ?_, ?_⟩
  · rintro (i | i)
    · exact hb i
    · exact Or.inl rfl
  · rintro (t | t)
    · rw [L.card_blockSupport_codeBlk_inl]; exact ho t
    · rw [L.card_blockSupport_codeBlk_inr]
      simp [blockSupport]
  · rw [hammingNorm_sum_elim, hammingNorm_zero, add_zero]
    exact hammingNorm_le_card_of_atMostOnePerBlock L.blk ho
  · rw [L.codeTarget_of_exists hex, L.mem_code_iff]
    have h0 : L.A hex.choose = L.rhs x := hex.choose_spec
    refine ⟨?_, fun i => by simp⟩
    have : (Sum.elim hex.choose 0 - Sum.elim v 0 : L.ι ⊕ L.ι → ZMod p) ∘ Sum.inl =
        hex.choose - v := by
      funext i; simp
    rw [this, map_sub, h0, hv, sub_self]

/-- NO instances (equation (B.1)): every codeword is far from the target. -/
theorem LinearSystemFamily.code_no {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hx : L.IsNo g x) :
    ∀ c ∈ L.code, g * L.numBlocks < hammingDist (L.codeTarget x) c := by
  intro c hc
  rw [L.mem_code_iff] at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hc_eq : c = Sum.elim (c ∘ Sum.inl) 0 := by
    funext i; rcases i with i | i
    · rfl
    · exact hc2 i
  by_cases hex : ∃ v, L.IsSolution x v
  · rw [L.codeTarget_of_exists hex, hc_eq, hammingDist_sum_elim, hammingDist_self, add_zero,
      hammingDist_comm, hammingDist_eq_hammingNorm]
    apply hx
    have h0 : L.A hex.choose = L.rhs x := hex.choose_spec
    show L.A (-(c ∘ Sum.inl) + hex.choose) = L.rhs x
    rw [map_add, map_neg, h0, hc1, neg_zero, zero_add]
  · rw [L.codeTarget_of_not_exists hex, hc_eq, hammingDist_sum_elim]
    have h1 : hammingDist (1 : L.ι → ZMod p) 0 = Fintype.card L.ι := by
      simp [hammingDist, Finset.card_univ]
    rw [h1, L.card_ι]
    have : g * L.numBlocks < L.numBlocks * L.blockSize := by
      rw [Nat.mul_comm L.numBlocks]; exact Nat.mul_lt_mul_of_pos_right hg hD
    omega

theorem LinearSystemFamily.codeDist_le_of_yes {x : X} (hx : L.IsYes x) :
    CodeFamily.codeDist (L.codeTarget x) L.code ≤ L.numBlocks := by
  obtain ⟨e, _, _, he, hmem⟩ := L.code_yes hx
  calc CodeFamily.codeDist (L.codeTarget x) L.code ≤ hammingDist (L.codeTarget x) (L.codeTarget x - e) :=
        CodeFamily.codeDist_le _ _ hmem
    _ = hammingNorm e := by
        rw [hammingDist_comm, hammingDist_eq_hammingNorm]
        congr 1
        abel
    _ ≤ L.numBlocks := he

theorem LinearSystemFamily.lt_codeDist_of_no {g : ℕ} (hg : g < L.blockSize)
    (hD : 0 < L.numBlocks) {x : X} (hx : L.IsNo g x) :
    g * L.numBlocks < CodeFamily.codeDist (L.codeTarget x) L.code :=
  CodeFamily.lt_codeDist_of_forall _ _ (L.code_no hg hD hx)

end OfSystem

section Extend

variable {p : ℕ} [Fact p.Prime] {X : Type} (F : Type) [Field F] [Algebra (ZMod p) F]

/-- The `F`-linear code spanned by a code over `𝔽_p`, with the targets mapped along
`algebraMap`. -/
noncomputable def CodeFamily.extend (C : CodeFamily (ZMod p) X) : CodeFamily F X where
  M := C.M
  code := Submodule.span F ((fun c : C.M → ZMod p => fun i => algebraMap (ZMod p) F (c i)) '' C.code)
  target := fun x i => algebraMap (ZMod p) F (C.target x i)

/-- Coordinatewise extension of scalars along `algebraMap`. -/
def CodeFamily.liftWord {M : Type} (c : M → ZMod p) : M → F := fun i => algebraMap (ZMod p) F (c i)

lemma CodeFamily.liftWord_mem_extend (C : CodeFamily (ZMod p) X) {c : C.M → ZMod p}
    (hc : c ∈ C.code) : CodeFamily.liftWord F c ∈ (C.extend F).code := by
  show CodeFamily.liftWord F c ∈ Submodule.span F
    ((fun c : C.M → ZMod p => fun i => algebraMap (ZMod p) F (c i)) '' C.code)
  exact Submodule.subset_span ⟨c, hc, rfl⟩

lemma CodeFamily.hammingDist_liftWord [DecidableEq F] {M : Type} [Fintype M] (y c : M → ZMod p) :
    hammingDist (CodeFamily.liftWord F y) (CodeFamily.liftWord F c) = hammingDist y c :=
  hammingDist_comp (fun _ => algebraMap (ZMod p) F) fun _ => (algebraMap (ZMod p) F).injective

/-- An `𝔽_p`-linear retraction `ρ : F → 𝔽_p` with `ρ ∘ algebraMap = id`. -/
lemma CodeFamily.exists_retraction (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] :
    ∃ ρ : F →ₗ[ZMod p] ZMod p, ∀ a : ZMod p, ρ (algebraMap (ZMod p) F a) = a := by
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (ZMod p) F)
    (LinearMap.ker_eq_bot.mpr (algebraMap (ZMod p) F).injective)
  exact ⟨ρ, fun a => by simpa using LinearMap.congr_fun hρ a⟩

/-- Every word of the extended code retracts to a word of the original code. -/
lemma CodeFamily.exists_retract_mem (C : CodeFamily (ZMod p) X) (ρ : F →ₗ[ZMod p] ZMod p)
    {c : C.M → F} (hc : c ∈ (C.extend F).code) :
    ∃ c' ∈ C.code, ∀ i, ρ (c i) = c' i := by
  simp only [CodeFamily.extend] at hc
  obtain ⟨n, a, g, hsum⟩ := Submodule.mem_span_set'.mp hc
  choose w hw using fun j : Fin n => (g j).2
  refine ⟨∑ j, ρ (a j) • w j, Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hw j).1,
    fun i => ?_⟩
  rw [← hsum]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← (hw j).2]
  show ρ (a j * algebraMap (ZMod p) F (w j i)) = ρ (a j) * w j i
  rw [mul_comm (a j), ← Algebra.smul_def, map_smul, smul_eq_mul]
  ring

/-- Extending scalars preserves the distance from a target over `𝔽_p` to the code
(proof of Lemma 3.7). -/
theorem CodeFamily.codeDist_extend [DecidableEq F] (C : CodeFamily (ZMod p) X) (x : X) :
    CodeFamily.codeDist ((C.extend F).target x) (C.extend F).code =
      CodeFamily.codeDist (C.target x) C.code := by
  have htarget : (C.extend F).target x = CodeFamily.liftWord F (C.target x) := rfl
  apply le_antisymm
  · obtain ⟨c, hc, hd⟩ := CodeFamily.exists_codeDist_eq (C.target x) C.code
    rw [← hd, htarget, ← CodeFamily.hammingDist_liftWord F]
    exact CodeFamily.codeDist_le _ _ (C.liftWord_mem_extend F hc)
  · obtain ⟨ρ, hρ⟩ := CodeFamily.exists_retraction F p
    obtain ⟨c, hc, hd⟩ := CodeFamily.exists_codeDist_eq ((C.extend F).target x) (C.extend F).code
    obtain ⟨c', hc', hcc'⟩ := C.exists_retract_mem F ρ hc
    rw [← hd]
    calc CodeFamily.codeDist (C.target x) C.code ≤ hammingDist (C.target x) c' :=
          CodeFamily.codeDist_le _ _ hc'
      _ = hammingDist (fun i => ρ ((C.extend F).target x i)) (fun i => ρ (c i)) := by
          congr 1
          · funext i; exact (hρ _).symm
          · funext i; exact (hcc' i).symm
      _ ≤ hammingDist ((C.extend F).target x) c := hammingDist_comp_le_hammingDist fun _ => ρ

end Extend

end LatticePrepro
