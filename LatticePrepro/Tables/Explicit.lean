import LatticePrepro.Basic.Nat
import LatticePrepro.Moments.Representation
import LatticePrepro.Verifier.Quadratic
import LatticePrepro.Tables.Digits
import LatticePrepro.Tables.FieldSetup
import LatticePrepro.Tables.Hankel
import LatticePrepro.Tables.PolyMatrixRank
import LatticePrepro.Tables.Construction
import LatticePrepro.Tables.ElementTable
import LatticePrepro.Tables.TableSoundness

/-!
# Explicit moment representations (Construction A.4, Theorem A.7)

For a prime `p` and integers `S ≥ 2`, `m ≥ 1`, `B ≥ 2`, we construct a finite field `K` of
characteristic `p`, an encoding tuple `ε` of length `S` over `K`, and a moment representation
over `K` with

* moment parameter `r = B^m`,
* `D = q` blocks of size `b = q^m`, where `q` is a power of `p` with
  `B ≤ q < 8 · p^3 · m · S · B`.

As in Construction A.4, `K = 𝕊(γ)` has degree `δ` over the sample field `𝕊` of size `q`, where
`δ` is the least power of `p` with `δ ≥ S` and `q` is the least power of `p` with
`q ≥ 8 p m B δ`. The represented coefficient functions live on an algebraic closure `Ω` of `K`.
The output is bundled as an `ExplicitMomentRepresentation`.

The ingredients are the construction (`Tables/Construction.lean`), completeness through the
element tables (`Tables/ElementTable.lean`), the rank analysis of the polynomial matrix
(`Tables/TableSoundness.lean`), and the Hankel reconstruction theorem (`Tables/Hankel.lean`).
-/

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d : ℕ}

/-- The encoding tuple `(0, 1, γ, …, γ^{S-1})` of a field setup of degree `δ ≥ S`. -/
noncomputable def encodingTuple {S δ : ℕ} (FS : FieldSetup p d δ) (hS : S ≤ δ) :
    EncodingTuple p FS.K S where
  E := fun i => if i = 0 then 0 else FS.γ ^ (i.val - 1)
  E_zero := by simp
  linearIndependent := by
    have := FS.linearIndependent_pow_zmod.comp (Fin.castLE hS) (Fin.castLE_injective hS)
    convert this using 1
    funext i
    simp [Fin.succ_ne_zero]

variable {δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

lemma card_fiber_snd (s : FS.𝕊) :
    (Finset.univ.filter fun i : Coord FS m => i.2 = s).card = Fintype.card (Fin m → FS.𝕊) := by
  rw [← Finset.card_univ]
  refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intro i hi i' hi' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    exact Prod.ext h (hi.trans hi'.symm)
  · intro lam _
    exact ⟨(lam, s), by simp, rfl⟩

variable {FS m B}

omit [Fact p.Prime] in
lemma maxOrder_eq (m B : ℕ) : 2 * hankelLen p (B ^ m) - 2 = maxOrder p m B := by
  unfold hankelLen maxOrder
  rw [mul_assoc]
  omega

lemma two_mul_sub_two_lt_hankelLen (hB : 2 ≤ B) {k : ℕ} (hk : k ≤ 2 * B ^ m - 2) :
    k < hankelLen p (B ^ m) := by
  unfold hankelLen
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1 : 1 ≤ B ^ m := Nat.one_le_pow _ _ (by omega)
  have : 2 * (B ^ m - 1) ≤ p * (B ^ m - 1) := Nat.mul_le_mul_right _ hp
  omega

/-- **Soundness** of the explicit moment representation. -/
theorem rep_sound (hB : 2 ≤ B) (hm : 1 ≤ m)
    (hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊) (y : Coord FS m → ZMod p)
    (hy : constraintFun FS m B y = 0) (hw : 2 * hammingNorm y < B ^ m * Fintype.card FS.𝕊) :
    ∃ f : AlgebraicClosure FS.K →₀ ZMod p,
      (∀ k ≤ 2 * B ^ m - 2,
        algebraMap FS.K (AlgebraicClosure FS.K) (mom FS m B y k) = moment f k) ∧
      Fintype.card FS.𝕊 * f.support.card ≤ 2 * hammingNorm y := by
  obtain ⟨t, htr, hqt, c, hc, hdep⟩ := soundness_setup hB hm hΔ hy hw
  set Ω := AlgebraicClosure FS.K
  let y' : ℕ → Ω := fun k => algebraMap FS.K Ω (mom FS m B y k)
  have hr : 2 ≤ B ^ m := le_trans hB (Nat.le_self_pow (by omega) B)
  have hfrob : ∀ k, p * k ≤ 2 * hankelLen p (B ^ m) - 2 → y' (p * k) = y' k ^ p := by
    intro k hk
    rw [maxOrder_eq] at hk
    simp only [y']
    rw [mom_mul_eq_pow_of_constraint hy hk, map_pow]
  have hdep' : ∃ c' : Fin (t + 1) → Ω, c' ≠ 0 ∧
      ∀ i : Fin (hankelLen p (B ^ m)), ∑ j, c' j * y' (i.val + j.val) = 0 := by
    refine ⟨fun j => algebraMap FS.K Ω (c j), ?_, ?_⟩
    · intro h0
      apply hc
      funext j
      have := congrFun h0 j
      simpa using (algebraMap FS.K Ω).injective (by simpa using this)
    · intro i
      simp only [y']
      rw [show (∑ x, algebraMap FS.K Ω (c x) * algebraMap FS.K Ω (mom FS m B y (i.val + x.val))) =
          algebraMap FS.K Ω (∑ x, c x * mom FS m B y (i.val + x.val)) by simp [map_sum, map_mul]]
      rw [hdep i, map_zero]
  obtain ⟨f, hf, hmom⟩ := hankel_reconstruction hr y' hfrob htr hdep'
  refine ⟨f, fun k hk => ?_, ?_⟩
  · exact hmom k (two_mul_sub_two_lt_hankelLen hB hk)
  · calc Fintype.card FS.𝕊 * f.support.card ≤ Fintype.card FS.𝕊 * t := Nat.mul_le_mul_left _ hf
      _ ≤ 2 * hammingNorm y := hqt

variable (FS m B)

/-- The explicit moment representation (Theorem A.7, representation part). -/
noncomputable def rep (hB : 2 ≤ B) (hm : 1 ≤ m)
    (hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊) :
    MomentRepresentation p FS.K (AlgebraicClosure FS.K) where
  r := B ^ m
  two_le_r := le_trans hB (Nat.le_self_pow (by omega) B)
  ι := Coord FS m
  β := FS.𝕊
  blk := Prod.snd
  blockSize := Fintype.card (Fin m → FS.𝕊)
  card_fiber := card_fiber_snd FS m
  W := ConstrW FS m B
  constraint := constraintₗ FS m B
  momentMap := fun k => momₗ FS m B k
  complete := fun α => by
    have hΔ' : degBound p m B δ < Fintype.card FS.𝕊 := by omega
    obtain ⟨h1, h2, h3, h4⟩ := elemTab_complete (FS := FS) hB hm hΔ' α
    exact ⟨elemTab FS m B α, h1, h2, h3, fun k => h4 k (by have := k.isLt; omega)⟩
  sound := fun y hy hw => by
    obtain ⟨f, hf, hcard⟩ := rep_sound hB hm hΔ y hy hw
    exact ⟨f, fun k => hf k (by have := k.isLt; omega), hcard⟩

end ExplicitTables

/-- The output of Theorem A.7: a field `K` of characteristic `p`, an encoding tuple of length `S`
over `K`, and a moment representation over `K` with `r = B^m` and `q` blocks of size `q^m`, where
`q` is a power of `p` with `B ≤ q < 8 p^3 m S B`. -/
structure ExplicitMomentRepresentation (p : ℕ) [Fact p.Prime] (S m B : ℕ) where
  /-- The moment field. -/
  K : Type
  [fieldK : Field K]
  [algK : Algebra (ZMod p) K]
  /-- The encoding tuple `(0, 1, γ, …, γ^{S-1})`. -/
  ε : EncodingTuple p K S
  /-- The moment representation; coefficient functions live on an algebraic closure of `K`. -/
  R : MomentRepresentation p K (AlgebraicClosure K)
  /-- The sample field size `q`, which is the number of blocks. -/
  q : ℕ
  r_eq : R.r = B ^ m
  numBlocks_eq : R.numBlocks = q
  blockSize_eq : R.blockSize = q ^ m
  q_eq_pow : ∃ d : ℕ, 1 ≤ d ∧ q = p ^ d
  le_q : B ≤ q
  q_lt : q < 8 * p ^ 3 * m * S * B

attribute [instance] ExplicitMomentRepresentation.fieldK ExplicitMomentRepresentation.algK

open ExplicitTables in
/-- **Theorem A.7** (explicit moment representations), existence form. -/
theorem exists_explicit_momentRepresentation (p : ℕ) [Fact p.Prime] (S m B : ℕ)
    (hS : 2 ≤ S) (hm : 1 ≤ m) (hB : 2 ≤ B) : Nonempty (ExplicitMomentRepresentation p S m B) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  -- the degree `δ`: the least power of `p` with `δ ≥ S`
  obtain ⟨e, -, hSδ, hδlt⟩ := exists_pow_between hp hS
  set δ := p ^ e with hδ
  have hδ1 : 1 ≤ δ := by omega
  -- the sample field size `q = p^d`: the least power of `p` with `q ≥ 8 p m B δ`
  have hpos : 0 < p * m * B * δ :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
  have hN : 2 ≤ 8 * p * m * B * δ := by
    calc 2 ≤ 8 := by norm_num
      _ ≤ 8 * (p * m * B * δ) := Nat.le_mul_of_pos_right 8 hpos
      _ = 8 * p * m * B * δ := by ring
  obtain ⟨d, hd1, hdN, hdlt⟩ := exists_pow_between hp hN
  obtain ⟨FS⟩ := FieldSetup.exists_fieldSetup p d δ hd1 hδ1
  have hq : Fintype.card FS.𝕊 = p ^ d := FS.card_𝕊
  have hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊 := by
    rw [hq]
    refine lt_of_lt_of_le ?_ hdN
    unfold degBound
    have hpm : 0 < 8 * p * m := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have hBδ : (B - 1) * (δ - 1) < B * δ :=
      calc (B - 1) * (δ - 1) ≤ (B - 1) * δ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ < B * δ := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    calc 4 * (2 * p * m * (B - 1) * (δ - 1)) = (8 * p * m) * ((B - 1) * (δ - 1)) := by ring
      _ < (8 * p * m) * (B * δ) := (Nat.mul_lt_mul_left hpm).mpr hBδ
      _ = 8 * p * m * B * δ := by ring
  refine ⟨⟨FS.K, encodingTuple FS hSδ, rep FS m B hB hm hΔ, Fintype.card FS.𝕊, rfl, rfl, ?_,
    ⟨d, hd1, hq⟩, ?_, ?_⟩⟩
  · show Fintype.card (Fin m → FS.𝕊) = Fintype.card FS.𝕊 ^ m
    rw [Fintype.card_fun, Fintype.card_fin]
  · calc B ≤ B * (8 * p * m * δ) := Nat.le_mul_of_pos_right B
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega))
      _ = 8 * p * m * B * δ := by ring
      _ ≤ p ^ d := hdN
      _ = Fintype.card FS.𝕊 := hq.symm
  · calc Fintype.card FS.𝕊 = p ^ d := hq
      _ < p * (8 * p * m * B * δ) := hdlt
      _ = 8 * p ^ 2 * m * B * δ := by ring
      _ ≤ 8 * p ^ 2 * m * B * (p * S) := Nat.mul_le_mul_left _ hδlt.le
      _ = 8 * p ^ 3 * m * S * B := by ring

end LatticePrepro
