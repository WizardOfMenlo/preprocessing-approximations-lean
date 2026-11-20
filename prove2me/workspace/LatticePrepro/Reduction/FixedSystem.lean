import LatticePrepro.Moments.Representation
import LatticePrepro.Verifier.Quadratic
import LatticePrepro.Reduction.LinearSystem

/-!
# The fixed-verifier linear system (Construction 4.5)

Given a quadratic verifier `V`, a moment representation `R` over `K` and an encoding tuple `ε`,
we build the linear system `A · v = b_x` of Construction 4.5:

* **Variables.** One evaluation table `v_T : R.ι → 𝔽_p` for every *table index* `T`: the product
  tables `v_{i,j}` for `0 ≤ j < i ≤ S` together with the main table `v_{0,0}` (`ProdIdx`), and the
  auxiliary tables `v^{(i)}` for `n + 1 < i ≤ S` (`AuxIdx`). Symmetric and diagonal indices refer
  to the same table through the representative map `rep`.
* **Equations.** The evaluation table constraints for every table, the encoding and gate moment
  equations of orders `k < r`, and the translation equations of orders `k ≤ 2r - 2`. Their
  left-hand sides (`encLhs`, `gateLhs`, `transLhs`) define both the predicate `Solves` and the
  linear map `sysMap`.

The main results are completeness and soundness (Theorem 4.6): the system is a gap reduction
from the language of `V` to the block-sparse linear-system problem with gap `g` whenever
`2 · g · N < r`, where `N` is the number of tables.
-/

namespace LatticePrepro

namespace QuadraticVerifier

variable {p : ℕ} (V : QuadraticVerifier p)

/-- Indices of the distinct product tables: pairs `(i, j)` with `j < i`, and `(0, 0)`. -/
abbrev ProdIdx : Type := {ij : Fin (V.S + 1) × Fin (V.S + 1) // ij.2 < ij.1 ∨ ij = (0, 0)}

/-- Indices of all evaluation tables of the system. -/
abbrev TblIdx : Type := V.ProdIdx ⊕ V.AuxIdx

/-- The index of the main table `v_{0,0}`. -/
def mainIdx : V.ProdIdx := ⟨(0, 0), Or.inr rfl⟩

/-- The representative of the product `z_i z_j`: `(max, min)` for `i ≠ j`, `(i, 0)` for `i = j ≠ 0`,
and `(0, 0)` for `i = j = 0`. -/
def rep (i j : Fin (V.S + 1)) : V.ProdIdx :=
  if h : j < i then ⟨(i, j), Or.inl h⟩
  else if h' : i < j then ⟨(j, i), Or.inl h'⟩
  else if h0 : i = 0 then ⟨(0, 0), Or.inr rfl⟩
  else ⟨(i, 0), Or.inl (Fin.pos_iff_ne_zero.mpr h0)⟩

lemma rep_of_lt {i j : Fin (V.S + 1)} (h : j < i) : V.rep i j = ⟨(i, j), Or.inl h⟩ := by
  simp [rep, h]

lemma rep_comm (i j : Fin (V.S + 1)) : V.rep i j = V.rep j i := by
  unfold rep
  rcases lt_trichotomy i j with h | h | h
  · have h' : ¬ j < i := lt_asymm h
    simp [h, h']
  · subst h; rfl
  · have h' : ¬ i < j := lt_asymm h
    simp [h, h']

lemma rep_diag (i : Fin (V.S + 1)) : V.rep i i = V.rep i 0 := by
  unfold rep
  by_cases h0 : i = 0
  · subst h0; simp
  · have hpos : (0 : Fin (V.S + 1)) < i := Fin.pos_iff_ne_zero.mpr h0
    simp [h0, hpos]

lemma rep_zero_zero : V.rep 0 0 = V.mainIdx := by
  simp [rep, mainIdx]

/-- Every product index is the representative of its own pair. -/
lemma rep_eq_self (T : V.ProdIdx) : V.rep T.1.1 T.1.2 = T := by
  obtain ⟨⟨i, j⟩, h⟩ := T
  rcases h with h | h
  · exact V.rep_of_lt h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact V.rep_zero_zero

/-- The number of tables is at most `(S + 1)^2`. -/
lemma card_tblIdx_le : Fintype.card V.TblIdx ≤ (V.S + 1) ^ 2 := by
  classical
  -- inject product indices as themselves and auxiliary indices `i` as the diagonal pair `(i, i)`
  let f : V.TblIdx → Fin (V.S + 1) × Fin (V.S + 1) := fun T =>
    match T with
    | Sum.inl ij => ij.1
    | Sum.inr i => (i.1, i.1)
  have hf : Function.Injective f := by
    rintro (⟨⟨a, b⟩, hab⟩ | ⟨a, ha⟩) (⟨⟨c, d⟩, hcd⟩ | ⟨c, hc⟩) h <;> simp only [f] at h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · exfalso
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases hab with hab | hab
      · exact lt_irrefl _ hab
      · simp only [Prod.mk.injEq] at hab
        have := hc
        rw [hab.1] at this
        simp at this
    · exfalso
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases hcd with hcd | hcd
      · exact lt_irrefl _ hcd
      · simp only [Prod.mk.injEq] at hcd
        have := ha
        rw [hcd.1] at this
        simp at this
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rfl
  simpa [sq] using Fintype.card_le_of_injective f hf

end QuadraticVerifier

section FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

namespace FixedSystem

/-- Columns of the system: a table index and a table coordinate. -/
abbrev Col : Type := V.TblIdx × R.ι

/-- The table with index `T` inside a vector of variables. -/
def tbl (v : Col V R → ZMod p) (T : V.TblIdx) : R.ι → ZMod p := fun i => v (T, i)

/-- The product table `v_{i,j}` (through the representative map). -/
def ptbl (v : Col V R → ZMod p) (i j : Fin (V.S + 1)) : R.ι → ZMod p :=
  tbl V R v (Sum.inl (V.rep i j))

/-- The auxiliary table `v^{(i)}`. -/
def atbl (v : Col V R → ZMod p) (i : V.AuxIdx) : R.ι → ZMod p := tbl V R v (Sum.inr i)

lemma tbl_add (v w : Col V R → ZMod p) (T : V.TblIdx) :
    tbl V R (v + w) T = tbl V R v T + tbl V R w T := rfl

lemma tbl_zero (T : V.TblIdx) : tbl V R (0 : Col V R → ZMod p) T = 0 := rfl

lemma tbl_smul (c : ZMod p) (v : Col V R → ZMod p) (T : V.TblIdx) :
    tbl V R (c • v) T = c • tbl V R v T := rfl

lemma ptbl_comm (v : Col V R → ZMod p) (i j : Fin (V.S + 1)) :
    ptbl V R v i j = ptbl V R v j i := by
  simp [ptbl, V.rep_comm i j]

lemma ptbl_diag (v : Col V R → ZMod p) (i : Fin (V.S + 1)) :
    ptbl V R v i i = ptbl V R v i 0 := by
  simp [ptbl, V.rep_diag i]

/-! ### The equations

Each family of equations is given by its left-hand side as a function of the variables; the
predicate `Solves` and the linear map `sysMap` are both defined from these, so they cannot drift
apart. -/

/-- Left-hand side of the encoding equation of order `k < r` for column `j`:
`M̂_{k+1}(v_{0,j}) - ∑ i, E_i M̂_k(v_{i,j})`. -/
def encLhs (v : Col V R → ZMod p) (j : Fin (V.S + 1)) (k : Fin R.r) : K :=
  R.momentMap (R.lowSucc k) (ptbl V R v 0 j) -
    ∑ i, ε.E i * R.momentMap (R.low k) (ptbl V R v i j)

/-- Left-hand side of the gate equation of gate `b` and order `k < r`:
`∑ i j, c^{(b)}_{ij} M̂_k(v_{i,j})`. -/
def gateLhs (v : Col V R → ZMod p) (b : Fin V.G) (k : Fin R.r) : K :=
  ∑ i, ∑ j, V.coeff b i j • R.momentMap (R.low k) (ptbl V R v i j)

/-- Left-hand side of the translation equation of order `k ≤ 2r - 2`:
`M̂_k(v_{0,0}) - ∑ i, ∑_{j < k} C(k, j) E_i^{k-j} M̂_j(v^{(i)})`. -/
def transLhs (v : Col V R → ZMod p) (k : R.Order) : K :=
  R.momentMap k (ptbl V R v 0 0) - ∑ i : V.AuxIdx, ∑ j : Fin k,
    ((k : ℕ).choose j : K) * ε.E i.1 ^ ((k : ℕ) - j) * R.momentMap (R.below k j) (atbl V R v i)

/-- The equations of Construction 4.5 for instance `x`, as a predicate on the variables. -/
structure Solves (x : Fin V.n → Bool) (v : Col V R → ZMod p) : Prop where
  /-- Evaluation table constraints for every table. -/
  constraint : ∀ T, R.constraint (tbl V R v T) = 0
  /-- Encoding equations of order `k < r`. -/
  encoding : ∀ (j : Fin (V.S + 1)) (k : Fin R.r), encLhs V R ε v j k = 0
  /-- Gate equations of order `k < r`. -/
  gate : ∀ (b : Fin V.G) (k : Fin R.r), gateLhs V R v b k = 0
  /-- Translation equations of order `k ≤ 2r - 2`. -/
  translation : ∀ k : R.Order, transLhs V R ε v k = V.instanceEnc ε x ^ (k : ℕ)

/-- The encoding equation, in the form `M̂_{k+1}(v_{0,j}) = ∑ i, E_i M̂_k(v_{i,j})`. -/
lemma Solves.encoding_eq {x : Fin V.n → Bool} {v : Col V R → ZMod p} (hv : Solves V R ε x v)
    (j : Fin (V.S + 1)) (k : Fin R.r) :
    R.momentMap (R.lowSucc k) (ptbl V R v 0 j) =
      ∑ i, ε.E i * R.momentMap (R.low k) (ptbl V R v i j) :=
  sub_eq_zero.mp (hv.encoding j k)

/-- The codomain of the system: rows for the table constraints, the encoding equations, the gate
equations, and the translation equations. -/
abbrev Rows : Type :=
  (V.TblIdx → R.W) × (Fin (V.S + 1) × Fin R.r → K) × (Fin V.G × Fin R.r → K) × (R.Order → K)

/-- The left-hand sides of all equations, as a function of the variables. -/
def sysFun (v : Col V R → ZMod p) : Rows V R :=
  (fun T => R.constraint (tbl V R v T),
   fun jk => encLhs V R ε v jk.1 jk.2,
   fun bk => gateLhs V R v bk.1 bk.2,
   fun k => transLhs V R ε v k)

lemma sysFun_zero : sysFun V R ε 0 = 0 := by
  simp only [sysFun, encLhs, gateLhs, transLhs, ptbl, atbl, tbl_zero, map_zero, mul_zero,
    smul_zero, Finset.sum_const_zero, sub_zero]
  rfl

lemma sysFun_add (v w : Col V R → ZMod p) :
    sysFun V R ε (v + w) = sysFun V R ε v + sysFun V R ε w := by
  simp only [sysFun, encLhs, gateLhs, transLhs, ptbl, atbl, tbl_add, map_add, Prod.mk_add_mk,
    Prod.mk.injEq]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · funext jk
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  · funext bk
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  · funext k
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring

/-- The system as an additive map. -/
def sysAddHom : (Col V R → ZMod p) →+ Rows V R where
  toFun := sysFun V R ε
  map_zero' := sysFun_zero V R ε
  map_add' := sysFun_add V R ε

/-- The fixed matrix `A` of Construction 4.5, as an `𝔽_p`-linear map. -/
def sysMap : (Col V R → ZMod p) →ₗ[ZMod p] Rows V R :=
  (sysAddHom V R ε).toZModLinearMap p

@[simp] lemma sysMap_apply (v : Col V R → ZMod p) : sysMap V R ε v = sysFun V R ε v := rfl

/-- The right-hand side `b_x`: zero except for the translation equations. -/
def sysRhs (x : Fin V.n → Bool) : Rows V R :=
  (0, 0, 0, fun k => V.instanceEnc ε x ^ (k : ℕ))

/-- `A v = b_x` holds exactly when `v` satisfies the equations of Construction 4.5. -/
theorem sysMap_eq_rhs_iff (x : Fin V.n → Bool) (v : Col V R → ZMod p) :
    sysMap V R ε v = sysRhs V R ε x ↔ Solves V R ε x v := by
  simp only [sysMap_apply, sysFun, sysRhs, Prod.mk.injEq, funext_iff, Pi.zero_apply, Prod.forall]
  exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

/-- The block of a column: the table index together with the block of the coordinate. -/
def blk (c : Col V R) : V.TblIdx × R.β := (c.1, R.blk c.2)

lemma card_fiber_blk (s : V.TblIdx × R.β) :
    (Finset.univ.filter fun c : Col V R => blk V R c = s).card = R.blockSize := by
  classical
  rw [← R.card_fiber s.2]
  refine Finset.card_bij (fun c _ => c.2) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, blk, Prod.ext_iff] at hc ⊢
    exact hc.2
  · intro c hc c' hc' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, blk, Prod.ext_iff] at hc hc'
    exact Prod.ext (hc.1.trans hc'.1.symm) h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨(s.1, i), by simp [blk, Prod.ext_iff, hi], rfl⟩

end FixedSystem

open FixedSystem in
/-- The fixed-verifier linear system of Construction 4.5 as a linear system family. -/
abbrev fixedSystem : LinearSystemFamily (ZMod p) (Fin V.n → Bool) where
  ι := Col V R
  β := V.TblIdx × R.β
  blk := FixedSystem.blk V R
  blockSize := R.blockSize
  card_fiber := card_fiber_blk V R
  W := Rows V R
  A := sysMap V R ε
  rhs := sysRhs V R ε

namespace FixedSystem

lemma isSolution_iff (x : Fin V.n → Bool) (v : Col V R → ZMod p) :
    (fixedSystem V R ε).IsSolution x v ↔ Solves V R ε x v :=
  sysMap_eq_rhs_iff V R ε x v

/-- The number of blocks of the system is `N · D`. -/
lemma numBlocks_eq : (fixedSystem V R ε).numBlocks = Fintype.card V.TblIdx * R.numBlocks :=
  Fintype.card_prod _ _

/-- The weight of a solution is the sum of the weights of its tables. -/
lemma hammingNorm_eq_sum_tbl (v : Col V R → ZMod p) :
    hammingNorm v = ∑ T, hammingNorm (tbl V R v T) := by
  classical
  unfold hammingNorm tbl
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun T _ => ?_
  refine Finset.card_bij (fun c _ => c.2) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [← hc.2]; exact hc.1
  · intro c hc c' hc' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    exact Prod.ext (hc.2.trans hc'.2.symm) h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨(T, i), by simpa using hi, rfl⟩

end FixedSystem

end FixedSystem

end LatticePrepro
