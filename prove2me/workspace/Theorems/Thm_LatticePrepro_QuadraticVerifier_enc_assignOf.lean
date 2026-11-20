import Mathlib
import Definitions.Def_LatticePrepro_Verifier_Quadratic

open LatticePrepro
open LatticePrepro.QuadraticVerifier
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
  (V : QuadraticVerifier p) (ε : EncodingTuple p K V.S)

theorem LatticePrepro.QuadraticVerifier.enc_assignOf (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) :
    ε.enc (V.assignOf x u) = V.instanceEnc ε x + ∑ i : V.AuxIdx, u i • ε.E i.1 := by sorry
