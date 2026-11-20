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
variable {x : Fin V.n → Bool} {v : Col V R → ZMod p} (hv : Solves V R ε x v)
  (f : V.TblIdx → Ω →₀ ZMod p)
  (hf : ∀ T (k : R.Order), algebraMap K Ω (R.momentMap k (tbl V R v T)) = moment (f T) k)
  (hN : ∑ T, (f T).support.card < R.r)
include hv hf hN

theorem LatticePrepro.FixedSystem.translation_pointwise (α : Ω) :
    algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) α) -
      ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (α - algebraMap K Ω (ε.E i.1))) -
        algebraMap (ZMod p) Ω (f (Sum.inr i) α)) -
      Finsupp.single (algebraMap K Ω (V.instanceEnc ε x)) (1 : Ω) α = 0 := by sorry
