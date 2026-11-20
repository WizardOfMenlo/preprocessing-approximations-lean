import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem

open LatticePrepro
open Finsupp
open LatticePrepro.FixedSystem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

theorem LatticePrepro.FixedSystem.recover {Fv : Fin (V.S + 1) → Fin (V.S + 1) → ZMod p}
    (hsymm : ∀ i j, Fv i j = Fv j i) (hdiag : ∀ i, Fv i i = Fv i 0) {α : Ω}
    (henc : ∀ j, α * algebraMap (ZMod p) Ω (Fv 0 j) =
      ∑ i, algebraMap K Ω (ε.E i) * algebraMap (ZMod p) Ω (Fv i j))
    (hgate : ∀ b, ∑ i, ∑ j, V.coeff b i j * Fv i j = 0) (hne : Fv 0 0 ≠ 0) :
    ∃ z : Fin (V.S + 1) → ZMod p, V.IsBooleanAssignment z ∧ V.IsValid z ∧
      algebraMap K Ω (ε.enc z) = α := by sorry
