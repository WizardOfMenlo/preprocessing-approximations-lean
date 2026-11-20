import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance

/-!
# Testing search outputs (Lemma 5.2)

For the code instances of Lemma 3.11 and the lattice instances of Lemma 3.12, a returned vector can
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

end LatticeReduction

end LatticePrepro
