import Mathlib

/-!
# Generalized digits (Definition A.1, Claim A.2)

Moment orders are written as exponent vectors `η : Fin m → ℕ` with
`val B η = ∑ h, η h * B ^ h`. The *generalized digit vector* of `k` is obtained by writing
`k = a · (B^m - 1) + b` with `0 ≤ b < B^m - 1` and taking `a · (B - 1)` plus the base-`B`
digits of `b`. It satisfies `val B (gdigits B m k) = k`, and for `k ≤ J · (B^m - 1)` all its
entries are at most `J · (B - 1)`.
-/

namespace LatticePrepro

/-- `val B η = ∑ h, η h * B ^ h`. -/
def digitVal (B : ℕ) {m : ℕ} (η : Fin m → ℕ) : ℕ := ∑ h : Fin m, η h * B ^ (h : ℕ)

/-- The generalized digit vector of `k` (Definition A.1). -/
def gdigits (B m k : ℕ) : Fin m → ℕ :=
  fun h => (k / (B ^ m - 1)) * (B - 1) + (k % (B ^ m - 1)) / B ^ (h : ℕ) % B

end LatticePrepro
