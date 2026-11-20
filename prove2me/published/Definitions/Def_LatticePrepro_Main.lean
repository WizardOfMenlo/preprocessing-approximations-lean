import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit

/-!
# Main results

* **Theorem 4.8** (`GapReduction`, `exists_gapReduction`): for every prime `p`, quadratic
  verifier `V` with `S` coordinates, gap `g ≥ 1` and `m ≥ 1`, there is a linear system family
  over `𝔽_p` that is a gap reduction from the language of `V` with gap `g`, with `g < b` and
  `n^m ≤ (8 p^4 m (S+1))^{(m+7) m} · g^{m+1}` columns.
* **Theorem 5.1** (`CodeGap`, `LatticeGap`, `code_gap`, `lattice_gap`, `exists_code_gap`,
  `exists_lattice_gap`): fixed codes over any finite field, and fixed lattices in any `ℓ_p`
  norm, with polynomial dimension `M ≤ (S + 1)^C` and approximation gap `M^{1/s - ε}` measured
  by `dist(t_x, 𝒞)` and `dist_p(t_x, Λ)`. The exponent `C = sizeExp p δ` is explicit
  (`δ = 1 - s ε`).

The polynomial-time computability claims of the paper are not formalized. In particular the
search test of Lemma 5.2 is stated for the concrete tests `CodeFamily.Accepts` and
`LatticeReduction.Accepts` (`Conversions/SearchTest.lean`) rather than as a field of `CodeGap` and
`LatticeGap`: without its running-time bound, an abstract "test" field would be satisfiable by
the membership predicate of `Lang` itself.
-/

namespace LatticePrepro

/-! ### Restricting an encoding tuple to fewer coordinates -/

/-! ### Theorem 4.8 -/

/-- The output of Theorem 4.8 for a verifier `V`, a gap `g` and `m ≥ 1`: a linear system family
`L` over `𝔽_p` that is a gap reduction from `L(V)` with gap `g < b` (`b` a power of `p`), with at
least one block and `n^m ≤ (8 p^4 m (S + 1))^{(m+7) m} · g^{m+1}` columns. -/
structure GapReduction (p : ℕ) [Fact p.Prime] (V : QuadraticVerifier p) (g m : ℕ) where
  /-- The fixed linear system. -/
  L : LinearSystemFamily (ZMod p) (Fin V.n → Bool)
  isGapReduction : L.IsGapReduction V.Language g
  lt_blockSize : g < L.blockSize
  blockSize_eq_pow : ∃ e : ℕ, L.blockSize = p ^ e
  numBlocks_pos : 0 < L.numBlocks
  card_pow_le : (Fintype.card L.ι) ^ m ≤ (8 * p ^ 4 * m * (V.S + 1)) ^ ((m + 7) * m) * g ^ (m + 1)

/-! ### Choice of parameters for Theorem 5.1

For a gap exponent `0 ≤ δ < 1` we choose `m` with `δ (1 + 1/m) < 1`, then the gap `g = (S+1)^k`
with `k` large enough that `64 · n^δ ≤ g`, and the size exponent `C` with `4 n ≤ (S+1)^C`, where
`n^m ≤ (8 p^4 m (S+1))^{(m+7) m} g^{m+1}` is the column bound of Theorem 4.8. All three
constants are explicit functions of `p` and `δ`. -/

/-- The number of moment axes `m = ⌈δ / (1 - δ)⌉ + 1`, so that `δ (m + 1) < m`. -/
noncomputable def momentAxes (δ : ℝ) : ℕ := ⌈δ / (1 - δ)⌉₊ + 1

/-- The exponent `a = (8 p^4 m + 1) (m + 7) m`, with `(8 p^4 m (S+1))^{(m+7) m} ≤ (S+1)^a`. -/
def prefactorExp (p m : ℕ) : ℕ := (8 * p ^ 4 * m + 1) * ((m + 7) * m)

/-- The gap exponent `k`, giving the gap `g = (S+1)^k`. -/
noncomputable def gapExp (p : ℕ) (δ : ℝ) : ℕ :=
  ⌈(6 * momentAxes δ + prefactorExp p (momentAxes δ) : ℝ) /
    (momentAxes δ - δ * (momentAxes δ + 1))⌉₊ + 1

/-- The size exponent `C`, giving `M ≤ (S+1)^C`. -/
noncomputable def sizeExp (p : ℕ) (δ : ℝ) : ℕ :=
  prefactorExp p (momentAxes δ) + gapExp p δ * (momentAxes δ + 1) + 2

/-! ### Theorem 5.1 for codes -/

/-- A fixed code with gap `M^{1 - ε}` for a language `Lang ⊆ X` with size parameter `n` and
exponent `C` (the conclusion of Theorem 5.1 for codes): a code `𝒞 ⊆ F^M` with `1 ≤ M ≤ n^C`,
targets `t_x` and an integer radius `R ≥ 1` such that `x ∈ Lang` implies `dist(t_x, 𝒞) ≤ R` and
`x ∉ Lang` implies `dist(t_x, 𝒞) > M^{1 - ε} · R`. -/
structure CodeGap (F : Type) [Field F] [DecidableEq F] (ε : ℝ) {X : Type} (Lang : Set X)
    (n C : ℕ) where
  /-- The fixed code and the targets. -/
  𝒞 : CodeFamily F X
  /-- The radius. -/
  R : ℕ
  one_le_R : 1 ≤ R
  one_le_card : 1 ≤ Fintype.card 𝒞.M
  card_le : Fintype.card 𝒞.M ≤ n ^ C
  yes : ∀ x ∈ Lang, CodeFamily.codeDist (𝒞.target x) 𝒞.code ≤ R
  no : ∀ x ∉ Lang,
    (Fintype.card 𝒞.M : ℝ) ^ (1 - ε) * R < CodeFamily.codeDist (𝒞.target x) 𝒞.code

/-! ### Theorem 5.1 for lattices -/

/-- A fixed lattice with gap `M^{1/s - ε}` in `ℓ_p` for a language `Lang ⊆ X` with size
parameter `n` and exponent `C` (the conclusion of Theorem 5.1 for lattices): a full-rank lattice
`Λ ⊆ ℤ^M` (containing `N · ℤ^M`) with `1 ≤ M ≤ n^C`, integer targets `t_x` and an integer radius
`R ≥ 1` such that `x ∈ Lang` implies `dist_p(t_x, Λ) ≤ R` and `x ∉ Lang` implies
`dist_p(t_x, Λ) > M^{1/s - ε} · R`. -/
structure LatticeGap (pn : PNorm) (ε : ℝ) {X : Type} (Lang : Set X) (n C : ℕ) where
  /-- The fixed lattice and the targets. -/
  Λ : LatticeFamily X
  /-- The radius. -/
  R : ℕ
  one_le_R : 1 ≤ R
  one_le_card : 1 ≤ Fintype.card Λ.M
  card_le : Fintype.card Λ.M ≤ n ^ C
  /-- The lattice contains `N · ℤ^M`. -/
  N : ℕ
  N_pos : 0 < N
  smul_mem : ∀ v : Λ.M → ℤ, (N : ℤ) • v ∈ Λ.lattice
  yes : ∀ x ∈ Lang, Λ.latticeDist pn x ≤ R
  no : ∀ x ∉ Lang, (Fintype.card Λ.M : ℝ) ^ (1 / pn.s - ε) * R < Λ.latticeDist pn x

end LatticePrepro
