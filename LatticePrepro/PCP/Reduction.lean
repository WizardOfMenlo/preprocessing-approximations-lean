import LatticePrepro.PCP.Code
import LatticePrepro.PCP.Inequality

/-!
# The PCP reduction (Theorem 6.4)

For the accepting-view code of Construction 6.2, built from a query-oblivious PCP `P` with perfect
completeness and soundness error `ε > 0` for a language `Lang`, an injective encoding map `E`
whose image has relative distance at least `δ`, and an integer `g < δ · ε^{-1/q}`:

* **Completeness** (`codeDist_le_of_mem`): `dist(y_x, 𝒞) ≤ Y` for `x ∈ Lang`;
* **Soundness** (`lt_codeDist_of_not_mem`): `dist(y_x, 𝒞) > g · Y` for `x ∉ Lang`;
* **Size** (`card_coord`): the block length is `(|Σ| + g) · Y + 1`,

where `Y = B · 2^ρ · q`. These are collected in `pcp_reduction`.

The proof follows the paper. The weight of `G₁ · v` is the sum over the queries `(r, j)` and the
symbols `a` of the weights of `E(v^{u_{r,j},a})` (equation (29), `hammingNorm_stackMap`). When
`G₀ · v = b_x` has a solution, the distance from the target to the code is the least such weight
over its solutions (equation (30)). For completeness, the indicator vector of the views of an
accepted proof is a solution of weight at most `Y`. For soundness, a solution `v` gives lists
`Λ_u = {a : v^{u,a} ≠ 0}`; a proof with entries in these lists is accepted for the random
string `r` whenever it agrees with a view of `r` that has predicate `V_{x,r}` and lies in the
support of `v`, and counting these proofs (in place of sampling one) bounds
`∑_r ∏_j |Λ_{u_{r,j}}|⁻¹` by `ε · 2^ρ`. The inequality of `LatticePrepro/PCP/Inequality.lean`
turns this into a lower bound on the total list size.

The running-time claims of Theorem 6.4 are not formalized.
-/

namespace LatticePrepro

/-- The Hamming weight of a vector on a product type is the sum of the weights of its slices. -/
lemma hammingNorm_prod {α β γ : Type*} [Fintype α] [Fintype β] [Zero γ] [DecidableEq γ]
    (f : α × β → γ) : hammingNorm f = ∑ a, hammingNorm fun b => f (a, b) := by
  simp only [hammingNorm, Finset.card_filter, Fintype.sum_prod_type]

namespace ObliviousPCP

variable {X : Type} (P : ObliviousPCP X) {F : Type} [Field F] [DecidableEq F] {B : ℕ}

/-- The weight of `G₁ · v` (equation (29)), with the copies indexed by the queries `(r, j)`. -/
lemma hammingNorm_stackMap (E : (P.Views → F) →ₗ[F] (Fin B → F)) (v : P.Views → F) :
    hammingNorm (P.stackMap E v) =
      ∑ r : P.Rand, ∑ j : Fin P.q, ∑ a : P.Alphabet,
        hammingNorm (E (P.restrict F (P.query r j) a v)) := by
  rw [hammingNorm_prod]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hammingNorm_prod]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hammingNorm_prod]
  rfl

/-- Two words padded by zeros are at the distance of their first blocks. -/
lemma hammingDist_pad {α β : Type} [Fintype α] [Fintype β] (a a' : α → F) :
    hammingDist (Sum.elim a (0 : β → F)) (Sum.elim a' 0) = hammingNorm (a - a') := by
  rw [hammingDist_sum_elim, hammingDist_self, add_zero, hammingNorm_sub_eq_hammingDist]

section Completeness

variable (x : X) (π : P.Proof) (hπ : ∀ r, P.Accepts x r π)

/-- The accepting view `(V_{x,r}, π|_{I_r})` of a proof that is accepted for every random
string. -/
def honestView (r : P.Rand) : P.View r :=
  ⟨(P.verifier x r, fun j => π (P.query r j)), hπ r, fun _ _ h => congrArg π h⟩

/-- The honest solution: the indicator vector of the views `(V_{x,r}, π|_{I_r})`. -/
def honest (F : Type) [Field F] : P.Views → F :=
  fun i => if i.2 = P.honestView x π hπ i.1 then 1 else 0

omit [DecidableEq F] in
/-- The honest solution satisfies the constraints (27). -/
lemma constraintMap_honest :
    P.constraintMap F (P.honest x π hπ F) = P.constraintRhs F x := by
  funext ⟨r, V⟩
  rw [constraintMap_apply, constraintRhs_apply, Finset.sum_eq_single (P.honestView x π hπ r)]
  · have h1 : (P.honestView x π hπ r).pred = P.verifier x r := rfl
    have h2 : P.honest x π hπ F ⟨r, P.honestView x π hπ r⟩ = 1 := ite_eq_left rfl
    rw [h1, h2]
    by_cases h : P.verifier x r = V
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  · intro w _ hw
    have h2 : P.honest x π hπ F ⟨r, w⟩ = 0 := ite_eq_right hw
    rw [h2, ite_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [DecidableEq F] in
/-- Every view in the support of the honest solution has answer `π(u)` at each of its queried
locations `u`, so `v^{u,a} = 0` for `a ≠ π(u)`. -/
lemma restrict_honest_eq_zero {u : Fin P.ℓ} {a : P.Alphabet} (ha : a ≠ π u) :
    P.restrict F u a (P.honest x π hπ F) = 0 := by
  funext i
  rw [restrict_apply]
  by_cases h : P.Hits u a i
  · rw [ite_eq_left h]
    obtain ⟨j, hj, hja⟩ := h
    refine ite_eq_right fun hi => ha ?_
    rw [← hja, hi, ← hj]
    rfl
  · rw [ite_eq_right h]
    rfl

/-- The honest solution has weight at most `Y`. -/
lemma hammingNorm_stackMap_honest_le (E : (P.Views → F) →ₗ[F] (Fin B → F)) :
    hammingNorm (P.stackMap E (P.honest x π hπ F)) ≤ P.radius B := by
  rw [P.hammingNorm_stackMap]
  calc ∑ r : P.Rand, ∑ j : Fin P.q, ∑ a : P.Alphabet,
        hammingNorm (E (P.restrict F (P.query r j) a (P.honest x π hπ F)))
      ≤ ∑ _r : P.Rand, ∑ _j : Fin P.q, B := by
        refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun j _ => ?_
        rw [Finset.sum_eq_single (π (P.query r j))]
        · exact hammingNorm_le_card_fintype.trans_eq (Fintype.card_fin B)
        · intro a _ ha
          rw [P.restrict_honest_eq_zero x π hπ ha, map_zero, hammingNorm_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = P.radius B := by
        simp only [Finset.sum_const, Finset.card_univ, P.card_rand, Fintype.card_fin, smul_eq_mul,
          radius]
        ring

end Completeness

/-- **Completeness of Theorem 6.4.** For `x ∈ Lang`, the target is within distance `Y` of the
code. -/
theorem codeDist_le_of_mem {Lang : Set X} (hc : P.PerfectlyComplete Lang)
    (E : (P.Views → F) →ₗ[F] (Fin B → F)) (g : ℕ) {x : X} (hx : x ∈ Lang) :
    CodeFamily.codeDist (P.target E g x) (P.code E g) ≤ P.radius B := by
  obtain ⟨π, hπ⟩ := hc x hx
  have hsol : P.constraintMap F (P.honest x π hπ F) = P.constraintRhs F x :=
    P.constraintMap_honest x π hπ
  have hex : ∃ v, P.constraintMap F v = P.constraintRhs F x := ⟨_, hsol⟩
  have hmem : Sum.elim (P.stackMap E (hex.choose - P.honest x π hπ F)) 0 ∈ P.code E g := by
    rw [P.mem_code_iff]
    exact ⟨_, by rw [map_sub, hex.choose_spec, hsol, sub_self], rfl⟩
  calc CodeFamily.codeDist (P.target E g x) (P.code E g)
      ≤ hammingDist (P.target E g x)
          (Sum.elim (P.stackMap E (hex.choose - P.honest x π hπ F)) 0) :=
        CodeFamily.codeDist_le _ _ hmem
    _ = hammingNorm (P.stackMap E (P.honest x π hπ F)) := by
        rw [P.target_of_exists E g hex, hammingDist_pad, ← map_sub, sub_sub_cancel]
    _ ≤ P.radius B := P.hammingNorm_stackMap_honest_le x π hπ E

/-- The heart of the soundness proof: for `x ∉ Lang`, every solution of `G₀ · v = b_x` has
weight `W(v) > g · Y`. -/
theorem lt_hammingNorm_stackMap_of_solution {Lang : Set X} {ε δ : ℝ}
    (hs : P.SoundnessError Lang ε) (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)}
    (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) {x : X} (hx : x ∉ Lang) {v : P.Views → F}
    (hv : P.constraintMap F v = P.constraintRhs F x) :
    g * P.radius B < hammingNorm (P.stackMap E v) := by
  classical
  -- For every random string, a view with predicate `V_{x,r}` in the support of `v`.
  have hview : ∀ r : P.Rand, ∃ w : P.View r, w.pred = P.verifier x r ∧ v ⟨r, w⟩ ≠ 0 := by
    intro r
    have h1 := congrFun hv ⟨r, P.verifier x r⟩
    rw [constraintMap_apply, constraintRhs_apply, ite_eq_left rfl] at h1
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1.trans_ne one_ne_zero)
    by_cases hp : w.pred = P.verifier x r
    · exact ⟨w, hp, by rwa [ite_eq_left hp] at hw⟩
    · rw [ite_eq_right hp] at hw
      exact absurd rfl hw
  choose w hwp hwv using hview
  -- The lists `Λ_u`, which contain the answers of these views.
  set Λ : Fin P.ℓ → Finset P.Alphabet :=
    fun u => Finset.univ.filter fun a => P.restrict F u a v ≠ 0 with hΛ
  have hΛmem : ∀ u a, a ∈ Λ u ↔ P.restrict F u a v ≠ 0 := fun u a => by
    simp only [hΛ, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmem : ∀ r j, (w r).ans j ∈ Λ (P.query r j) := by
    intro r j
    rw [hΛmem]
    intro h0
    have h1 := congrFun h0 ⟨r, w r⟩
    have hit : P.Hits (P.query r j) ((w r).ans j) ⟨r, w r⟩ := ⟨j, rfl, rfl⟩
    rw [restrict_apply, ite_eq_left hit] at h1
    exact hwv r h1
  -- Proofs with entries in the lists (a fixed symbol at the locations with an empty list).
  let r₀ : P.Rand := fun _ => false
  let a₀ : P.Alphabet := (w r₀).ans ⟨0, P.q_pos⟩
  set L : Fin P.ℓ → Finset P.Alphabet :=
    fun u => if (Λ u).Nonempty then Λ u else {a₀} with hL
  have hLq : ∀ r j, L (P.query r j) = Λ (P.query r j) := fun r j => by
    simp only [hL]
    rw [ite_eq_left ⟨_, hmem r j⟩]
  have hLne : ∀ u, (L u).Nonempty := fun u => by
    simp only [hL]
    split_ifs with h
    · exact h
    · exact Finset.singleton_nonempty _
  set S : Finset P.Proof := Fintype.piFinset L with hS
  have hSpos : 0 < S.card := by
    rw [hS, Fintype.card_piFinset]
    exact Finset.prod_pos fun u _ => (hLne u).card_pos
  -- For every random string, at least a `∏_j |Λ_{u_{r,j}}|⁻¹` fraction of these proofs is
  -- accepted: overwriting a proof with the answers of the view `w r` gives an accepted proof.
  have hcount : ∀ r : P.Rand, S.card ≤
      (S.filter fun π => P.Accepts x r π).card * ∏ j, (Λ (P.query r j)).card := by
    intro r
    let ov : P.Proof → P.Proof :=
      fun π u => if h : ∃ j, P.query r j = u then (w r).ans h.choose else π u
    have hov : ∀ π j, ov π (P.query r j) = (w r).ans j := by
      intro π j
      have h : ∃ j', P.query r j' = P.query r j := ⟨j, rfl⟩
      show (if h : ∃ j', P.query r j' = P.query r j then (w r).ans h.choose
        else π (P.query r j)) = (w r).ans j
      rw [dite_eq_left h]
      exact (w r).ans_eq h.choose_spec
    have hov' : ∀ π u, (¬ ∃ j, P.query r j = u) → ov π u = π u := fun π u h => dite_eq_right h
    have hinj : Set.InjOn (fun π : P.Proof => (ov π, fun j => π (P.query r j)))
        (S : Set P.Proof) := by
      intro π₁ _ π₂ _ h
      have h1 : ov π₁ = ov π₂ := congrArg Prod.fst h
      have h2 : (fun j => π₁ (P.query r j)) = fun j => π₂ (P.query r j) := congrArg Prod.snd h
      funext u
      by_cases hu : ∃ j, P.query r j = u
      · obtain ⟨j, rfl⟩ := hu
        exact congrFun h2 j
      · rw [← hov' π₁ u hu, ← hov' π₂ u hu, h1]
    have hmaps : ∀ π ∈ S, (fun π : P.Proof => (ov π, fun j => π (P.query r j))) π ∈
        (S.filter fun π => P.Accepts x r π) ×ˢ Fintype.piFinset fun j => Λ (P.query r j) := by
      intro π hπ
      rw [hS, Fintype.mem_piFinset] at hπ
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · show ov π ∈ S
        rw [hS, Fintype.mem_piFinset]
        intro u
        by_cases hu : ∃ j, P.query r j = u
        · obtain ⟨j, rfl⟩ := hu
          rw [hov, hLq]
          exact hmem r j
        · rw [hov' π u hu]
          exact hπ u
      · show P.eval r (P.verifier x r) (fun j => ov π (P.query r j)) = true
        have h1 : (fun j => ov π (P.query r j)) = (w r).ans := funext fun j => hov π j
        rw [h1, ← hwp r]
        exact (w r).eval_eq
      · show (fun j => π (P.query r j)) ∈ Fintype.piFinset fun j => Λ (P.query r j)
        rw [Fintype.mem_piFinset]
        intro j
        rw [← hLq]
        exact hπ _
    calc S.card ≤ ((S.filter fun π => P.Accepts x r π) ×ˢ
          Fintype.piFinset fun j => Λ (P.query r j)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = (S.filter fun π => P.Accepts x r π).card * ∏ j, (Λ (P.query r j)).card := by
          rw [Finset.card_product, Fintype.card_piFinset]
  -- Soundness of the PCP bounds the number of accepted pairs (equation (31), first step).
  set lam : P.Rand → Fin P.q → ℝ := fun r j => ((Λ (P.query r j)).card : ℝ) with hlam
  have hlampos : ∀ r j, 0 < lam r j := fun r j => by
    simp only [hlam]
    exact_mod_cast Finset.card_pos.mpr ⟨_, hmem r j⟩
  have hsum : ∑ r, ∏ j, (lam r j)⁻¹ ≤ ε * 2 ^ P.ρ := by
    have h1 : ∀ r : P.Rand, (S.card : ℝ) * ∏ j, (lam r j)⁻¹ ≤
        ((S.filter fun π => P.Accepts x r π).card : ℝ) := by
      intro r
      have hp : 0 < ∏ j, lam r j := Finset.prod_pos fun j _ => hlampos r j
      rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, div_le_iff₀ hp]
      have h' : ((S.card : ℕ) : ℝ) ≤
          (((S.filter fun π => P.Accepts x r π).card * ∏ j, (Λ (P.query r j)).card : ℕ) : ℝ) :=
        Nat.cast_le.mpr (hcount r)
      rw [Nat.cast_mul, Nat.cast_prod] at h'
      exact h'
    have h2 : (∑ r : P.Rand, ((S.filter fun π => P.Accepts x r π).card : ℝ)) =
        ∑ π ∈ S, ((Finset.univ.filter fun r => P.Accepts x r π).card : ℝ) := by
      simp only [Finset.card_filter, Nat.cast_sum]
      rw [Finset.sum_comm]
    have h3 : ∑ π ∈ S, ((Finset.univ.filter fun r => P.Accepts x r π).card : ℝ) ≤
        S.card * (ε * 2 ^ P.ρ) := by
      calc ∑ π ∈ S, ((Finset.univ.filter fun r => P.Accepts x r π).card : ℝ)
          ≤ ∑ _π ∈ S, ε * 2 ^ P.ρ := Finset.sum_le_sum fun π _ => hs x hx π
        _ = S.card * (ε * 2 ^ P.ρ) := by rw [Finset.sum_const, nsmul_eq_mul]
    have h4 : (S.card : ℝ) * ∑ r, ∏ j, (lam r j)⁻¹ ≤ S.card * (ε * 2 ^ P.ρ) := by
      rw [Finset.mul_sum]
      exact (Finset.sum_le_sum fun r _ => h1 r).trans (h2.le.trans h3)
    exact le_of_mul_le_mul_left h4 (Nat.cast_pos.mpr hSpos)
  -- The total list size is at least `2^ρ · q · ε^{-1/q}` (equation (31)).
  set t : ℝ := ε ^ (-(1 : ℝ) / P.q) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hε _
  have hq0 : (P.q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr P.q_pos.ne'
  have htq : t ^ P.q = ε⁻¹ := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hε.le, div_mul_cancel₀ _ hq0, Real.rpow_neg_one]
  have hcard : (Fintype.card P.Rand : ℝ) = 2 ^ P.ρ := by
    rw [P.card_rand]
    push_cast
    rfl
  have hkey : (2 : ℝ) ^ P.ρ * P.q * t ≤ ∑ r, ∑ j, lam r j := by
    have h1 : (∑ r, ∏ j, (lam r j)⁻¹) * t ^ P.q ≤ Fintype.card P.Rand := by
      rw [htq, hcard]
      calc (∑ r, ∏ j, (lam r j)⁻¹) * ε⁻¹ ≤ ε * 2 ^ P.ρ * ε⁻¹ :=
            mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hε.le)
        _ = 2 ^ P.ρ := by
            field_simp
    have h2 := mul_le_sum_of_sum_prod_inv_le lam hlampos htpos h1
    rwa [hcard] at h2
  -- The encoding has `B ≥ 1` coordinates, since it is injective on a nonzero space.
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with rfl | h
    · exfalso
      have hne := (hΛmem _ _).mp (hmem r₀ ⟨0, P.q_pos⟩)
      exact hne (hE (Subsingleton.elim _ _))
    · exact h
  have hδpos : 0 < δ := by
    by_contra h
    have h1 : δ * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) htpos.le
    have h2 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
    linarith
  -- Every symbol of a list contributes weight at least `δ · B` (equation (29)).
  have hweight : δ * B * ∑ r, ∑ j, lam r j ≤ (hammingNorm (P.stackMap E v) : ℝ) := by
    rw [P.hammingNorm_stackMap, Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Nat.cast_sum]
    calc δ * B * lam r j = ∑ _a ∈ Λ (P.query r j), δ * B := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ a ∈ Λ (P.query r j),
            (hammingNorm (E (P.restrict F (P.query r j) a v)) : ℝ) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have hne : P.restrict F (P.query r j) a v ≠ 0 := (hΛmem _ _).mp ha
          exact hδ _ (LinearMap.mem_range.mpr ⟨_, rfl⟩)
            (fun h0 => hne (hE (h0.trans (map_zero E).symm)))
      _ ≤ ∑ a, (hammingNorm (E (P.restrict F (P.query r j) a v)) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => Nat.cast_nonneg _
  have hY : (0 : ℝ) < (P.radius B : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (Nat.mul_pos hB (pow_pos (by norm_num) _)) P.q_pos)
  have hfinal : (g : ℝ) * P.radius B < (hammingNorm (P.stackMap E v) : ℝ) := by
    calc (g : ℝ) * P.radius B < δ * t * P.radius B := mul_lt_mul_of_pos_right hg hY
      _ = δ * B * ((2 : ℝ) ^ P.ρ * P.q * t) := by
          simp only [radius]
          push_cast
          ring
      _ ≤ δ * B * ∑ r, ∑ j, lam r j :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg hδpos.le (Nat.cast_nonneg B))
      _ ≤ (hammingNorm (P.stackMap E v) : ℝ) := hweight
  exact_mod_cast hfinal

/-- **Soundness of Theorem 6.4.** For `x ∉ Lang`, the target is at distance more than `g · Y`
from the code. -/
theorem lt_codeDist_of_not_mem {Lang : Set X} {ε δ : ℝ} (hs : P.SoundnessError Lang ε)
    (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)} (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) {x : X} (hx : x ∉ Lang) :
    g * P.radius B < CodeFamily.codeDist (P.target E g x) (P.code E g) := by
  apply CodeFamily.lt_codeDist_of_forall
  intro c hc
  obtain ⟨v', hv', rfl⟩ := (P.mem_code_iff E g c).mp hc
  by_cases hex : ∃ v, P.constraintMap F v = P.constraintRhs F x
  · rw [P.target_of_exists E g hex, hammingDist_pad, ← map_sub]
    exact P.lt_hammingNorm_stackMap_of_solution hs hε hE hδ hg hx
      (by rw [map_sub, hex.choose_spec, hv', sub_zero])
  · rw [P.target_of_not_exists E g hex, hammingDist_sum_elim]
    have h1 : hammingDist (1 : Fin (g * P.radius B + 1) → F) 0 = g * P.radius B + 1 := by
      simp [hammingDist]
    omega

/-- **Theorem 6.4** (the PCP reduction). Let `P` be a query-oblivious PCP with perfect
completeness and soundness error `ε > 0` for `Lang`, let `E : F^m → F^B` be an injective linear
map whose image has relative distance at least `δ`, and let `g < δ · ε^{-1/q}`. Then the
accepting-view code `𝒞` and the targets `y_x` of Construction 6.2 satisfy, with
`Y = B · 2^ρ · q`:

* `dist(y_x, 𝒞) ≤ Y` for every `x ∈ Lang`;
* `dist(y_x, 𝒞) > g · Y` for every `x ∉ Lang`;
* the block length is `(|Σ| + g) · Y + 1`.

The code does not depend on `x`. -/
theorem pcp_reduction {Lang : Set X} {ε δ : ℝ} (hc : P.PerfectlyComplete Lang)
    (hs : P.SoundnessError Lang ε) (hε : 0 < ε) {E : (P.Views → F) →ₗ[F] (Fin B → F)}
    (hE : Function.Injective E)
    (hδ : ∀ c ∈ LinearMap.range E, c ≠ 0 → δ * B ≤ hammingNorm c) {g : ℕ}
    (hg : (g : ℝ) < δ * ε ^ (-(1 : ℝ) / P.q)) :
    (∀ x ∈ Lang, CodeFamily.codeDist (P.target E g x) (P.code E g) ≤ P.radius B) ∧
    (∀ x, x ∉ Lang → g * P.radius B < CodeFamily.codeDist (P.target E g x) (P.code E g)) ∧
    Fintype.card (P.Coord B ⊕ Fin (g * P.radius B + 1)) =
      (Fintype.card P.Alphabet + g) * P.radius B + 1 :=
  ⟨fun _ hx => P.codeDist_le_of_mem hc E g hx,
    fun _ hx => P.lt_codeDist_of_not_mem hs hε hE hδ hg hx, P.card_coord B g⟩

end ObliviousPCP

end LatticePrepro
