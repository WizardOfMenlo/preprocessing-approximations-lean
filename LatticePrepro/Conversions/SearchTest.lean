import LatticePrepro.Conversions.Codes
import LatticePrepro.Conversions.Lattices
import LatticePrepro.Lattices.Distance

/-!
# Testing search outputs (Lemma 5.2)

For the code instances of Lemma 3.7 and the lattice instances of Lemma 3.8, a returned vector can
be tested: it is *accepted* if it lies in the code or lattice and its residual weight `w` is at
most `g · D`, where `w = dist(t_x, v)` for codes and `w` is the residual weight of the
`LatticeReduction` for lattices. Then

* on YES instances, every `f`-approximate solution is accepted (for `f < g` for codes and
  `16 · f^s ≤ g` for lattices);
* on NO instances, every vector is rejected.

The paper's computability claim (the test runs in polynomial time) is not formalized.
-/

namespace LatticePrepro

/-! ### Codes -/

namespace CodeFamily

variable {F : Type} [Field F] [DecidableEq F] {X : Type} (C : CodeFamily F X)

/-- The test of Lemma 5.2 for codes: a codeword is accepted if its Hamming distance from the
target is at most `g · R`. -/
def Accepts (g R : ℕ) (x : X) (c : C.M → F) : Prop :=
  c ∈ C.code ∧ hammingDist (C.target x) c ≤ g * R

/-- An `f`-approximate solution: a codeword within distance `f · dist(t_x, 𝒞)` of the target. -/
def IsApprox (f : ℝ) (x : X) (c : C.M → F) : Prop :=
  c ∈ C.code ∧ (hammingDist (C.target x) c : ℝ) ≤ f * codeDist (C.target x) C.code

/-- **Lemma 5.2 for codes, YES instances**: if `dist(t_x, 𝒞) ≤ R` and `f ≤ g`, every
`f`-approximate solution is accepted. -/
theorem accepts_of_isApprox {g R : ℕ} {x : X} (hx : codeDist (C.target x) C.code ≤ R) {f : ℝ}
    (hfg : f ≤ g) {c : C.M → F} (hc : C.IsApprox f x c) : C.Accepts g R x c := by
  refine ⟨hc.1, ?_⟩
  have h : (hammingDist (C.target x) c : ℝ) ≤ (g : ℝ) * R :=
    calc (hammingDist (C.target x) c : ℝ) ≤ f * codeDist (C.target x) C.code := hc.2
      _ ≤ g * R := by gcongr
  exact_mod_cast h

/-- **Lemma 5.2 for codes, NO instances**: if `dist(t_x, 𝒞) > g · R`, every vector is rejected. -/
theorem not_accepts_of_lt {g R : ℕ} {x : X} (hx : g * R < codeDist (C.target x) C.code)
    (c : C.M → F) : ¬ C.Accepts g R x c := by
  rintro ⟨hc, hd⟩
  exact absurd (codeDist_le (C.target x) C.code hc) (by omega)

end CodeFamily

/-! ### Lattices -/

namespace LatticeReduction

variable {p : ℕ} [Fact p.Prime] {X : Type} {L : LinearSystemFamily (ZMod p) X} {g : ℕ}
  {pn : PNorm} (Red : LatticeReduction L g pn)

/-- The test of Lemma 5.2 for lattices: a lattice vector is accepted if its residual weight is at
most `g · D`. -/
def Accepts (x : X) (v : Red.Λ.M → ℤ) : Prop :=
  v ∈ Red.Λ.lattice ∧ Red.weight x v ≤ g * L.numBlocks

/-- An `f`-approximate solution: a lattice vector within distance `f · dist_p(t_x, Λ)` of the
target. -/
def IsApprox (f : ℝ) (x : X) (v : Red.Λ.M → ℤ) : Prop :=
  v ∈ Red.Λ.lattice ∧ Red.Λ.dist pn x v ≤ f * Red.Λ.latticeDist pn x

/-- **Lemma 5.2 for lattices, YES instances**: if `16 · f^s ≤ g`, every `f`-approximate solution
to a YES instance is accepted. -/
theorem accepts_of_isApprox {f : ℝ} (hf : 0 ≤ f) (hgf : 16 * f ^ pn.s ≤ g) {x : X}
    (hx : L.IsYes x) {v : Red.Λ.M → ℤ} (hv : Red.IsApprox f x v) : Red.Accepts x v := by
  refine ⟨hv.1, ?_⟩
  have hR : (0 : ℝ) < Red.R := by exact_mod_cast Red.one_le_R
  have hD : (0 : ℝ) ≤ L.numBlocks := by positivity
  have hs : 0 ≤ pn.s := by linarith [pn.one_le_s]
  -- `dist ≤ f · dist(t_x, Λ) ≤ f · R`
  have hdist : Red.Λ.dist pn x v / Red.R ≤ f := by
    rw [div_le_iff₀ hR]
    calc Red.Λ.dist pn x v ≤ f * Red.Λ.latticeDist pn x := hv.2
      _ ≤ f * Red.R := by
          gcongr
          exact Red.Λ.latticeDist_le_of_exists pn x (Red.yes x hx)
  have h : (Red.weight x v : ℝ) ≤ (g : ℝ) * L.numBlocks :=
    calc (Red.weight x v : ℝ) ≤ 16 * L.numBlocks * (Red.Λ.dist pn x v / Red.R) ^ pn.s :=
          Red.weight_le x v hv.1
      _ ≤ 16 * L.numBlocks * f ^ pn.s := by
          gcongr
          · exact div_nonneg (Red.Λ.dist_nonneg pn x v) hR.le
      _ = (16 * f ^ pn.s) * L.numBlocks := by ring
      _ ≤ g * L.numBlocks := by gcongr
  exact_mod_cast h

/-- **Lemma 5.2 for lattices, NO instances**: every vector is rejected. -/
theorem not_accepts_of_isNo {x : X} (hx : L.IsNo g x) (v : Red.Λ.M → ℤ) : ¬ Red.Accepts x v := by
  rintro ⟨hv, hw⟩
  exact absurd (Red.lt_weight x hx v hv) (by omega)

end LatticeReduction

end LatticePrepro
