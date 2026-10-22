import Mathlib

/-!
# Walsh–Hadamard matrices and the block Hadamard map (Lemma B.3)

The Walsh–Hadamard matrix of order `2^k` is indexed by `Idx k = Fin k → ZMod 2`, with entries
`wh u w = (-1)^{⟨u, w⟩}`. It is symmetric with `H * H = 2^k • 1`. The block Hadamard map
`blockHad` applies `H` to every block of a vector indexed by `β × Idx k`; it is `ℤ`-linear,
satisfies `blockHad (blockHad v) = 2^k • v` and Parseval's identity
`∑ (blockHad v)² = 2^k ∑ v²`, and has entries bounded by the `ℓ_1` norm of the block.
-/

namespace LatticePrepro

namespace Hadamard

/-- The sign character `ZMod 2 → ℤ`, `0 ↦ 1`, `1 ↦ -1`. -/
def sgn (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

@[simp] lemma sgn_zero : sgn 0 = 1 := rfl

lemma sgn_one : sgn 1 = -1 := by decide

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  revert a b; decide

lemma abs_sgn (a : ZMod 2) : |sgn a| = 1 := by
  unfold sgn; split_ifs <;> simp

lemma zmod2_eq_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

lemma zmod2_add_eq_zero_iff : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide

variable (k : ℕ)

/-- The index set of a Hadamard block of size `2^k`. -/
abbrev Idx : Type := Fin k → ZMod 2

lemma card_Idx : Fintype.card (Idx k) = 2 ^ k := by
  simp [ZMod.card]

/-- The inner product `⟨u, w⟩ = ∑ u_i w_i` over `ZMod 2`. -/
def ip (u w : Idx k) : ZMod 2 := ∑ i, u i * w i

/-- Entries `(-1)^{⟨u, w⟩}` of the Walsh–Hadamard matrix. -/
def wh (u w : Idx k) : ℤ := sgn (ip k u w)

lemma ip_comm (u w : Idx k) : ip k u w = ip k w u := by
  simp [ip, mul_comm]

lemma ip_add_right (u w w' : Idx k) : ip k u (w + w') = ip k u w + ip k u w' := by
  simp [ip, mul_add, Finset.sum_add_distrib]

lemma ip_zero_right (u : Idx k) : ip k u 0 = 0 := by simp [ip]

lemma ip_add_single (u d : Idx k) (i : Fin k) :
    ip k (u + Pi.single i 1) d = ip k u d + d i := by
  simp [ip, add_mul, Finset.sum_add_distrib, Pi.single_apply]

lemma wh_comm (u w : Idx k) : wh k u w = wh k w u := by
  rw [wh, wh, ip_comm]

lemma wh_mul_wh (u w w' : Idx k) : wh k u w * wh k u w' = wh k u (w + w') := by
  rw [wh, wh, wh, ip_add_right, sgn_add]

lemma abs_wh (u w : Idx k) : |wh k u w| = 1 := abs_sgn _

lemma idx_add_eq_zero_iff (w w' : Idx k) : w + w' = 0 ↔ w = w' := by
  constructor
  · intro h; funext i; exact (zmod2_add_eq_zero_iff _ _).mp (congrFun h i)
  · rintro rfl; funext i; exact (zmod2_add_eq_zero_iff _ _).mpr rfl

/-- The character sum `∑_u (-1)^{⟨u, d⟩}` is `2^k` for `d = 0` and `0` otherwise. -/
lemma sum_sgn_ip (d : Idx k) : ∑ u, sgn (ip k u d) = if d = 0 then (2 ^ k : ℤ) else 0 := by
  split_ifs with hd
  · subst hd
    simp [ip_zero_right, Finset.card_univ]
  · obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hd (funext h)
    have hdi : d i = 1 := zmod2_eq_one_of_ne_zero _ hi
    have key : ∀ u, sgn (ip k (u + Pi.single i 1) d) = - sgn (ip k u d) := by
      intro u
      rw [ip_add_single, hdi, sgn_add, sgn_one]
      ring
    have h := Equiv.sum_comp (Equiv.addRight (Pi.single i (1 : ZMod 2)))
      (fun u => sgn (ip k u d))
    simp only [Equiv.coe_addRight, key, Finset.sum_neg_distrib] at h
    linarith

/-- Orthogonality of the Walsh–Hadamard matrix. -/
lemma sum_wh_mul_wh (w w' : Idx k) :
    ∑ u, wh k u w * wh k u w' = if w = w' then (2 ^ k : ℤ) else 0 := by
  simp_rw [wh_mul_wh]
  unfold wh
  rw [sum_sgn_ip]
  simp only [idx_add_eq_zero_iff]

/-- The Walsh–Hadamard matrix. -/
def whMat : Matrix (Idx k) (Idx k) ℤ := Matrix.of fun u w => wh k u w

lemma whMat_transpose : (whMat k).transpose = whMat k := by
  ext u w; simp [whMat, wh_comm]

lemma whMat_mul_whMat : whMat k * whMat k = (2 ^ k : ℤ) • (1 : Matrix (Idx k) (Idx k) ℤ) := by
  ext w w'
  simp only [Matrix.mul_apply, whMat, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl fun u _ => by rw [wh_comm k w u]]
  exact sum_wh_mul_wh k w w'

/-- `‖H x‖₂² = 2^k ‖x‖₂²`. -/
lemma dotProduct_mulVec_self (x : Idx k → ℤ) :
    ((whMat k).mulVec x) ⬝ᵥ ((whMat k).mulVec x) = (2 ^ k : ℤ) * (x ⬝ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, whMat_transpose,
    Matrix.mulVec_mulVec, whMat_mul_whMat, Matrix.smul_mulVec, Matrix.one_mulVec,
    smul_dotProduct, smul_eq_mul]

section Block

variable {β : Type*}

/-- The block Hadamard map: apply the Walsh–Hadamard matrix to every block. -/
def blockHad (v : β × Idx k → ℤ) : β × Idx k → ℤ :=
  fun su => (whMat k).mulVec (fun w => v (su.1, w)) su.2

lemma blockHad_apply (v : β × Idx k → ℤ) (su : β × Idx k) :
    blockHad k v su = ∑ w, wh k su.2 w * v (su.1, w) := by
  simp [blockHad, Matrix.mulVec, dotProduct, whMat]

lemma blockHad_add (v w : β × Idx k → ℤ) : blockHad k (v + w) = blockHad k v + blockHad k w := by
  funext su; simp [blockHad_apply, mul_add, Finset.sum_add_distrib]

lemma blockHad_sub (v w : β × Idx k → ℤ) : blockHad k (v - w) = blockHad k v - blockHad k w := by
  funext su; simp [blockHad_apply, mul_sub, Finset.sum_sub_distrib]

lemma blockHad_smul (c : ℤ) (v : β × Idx k → ℤ) : blockHad k (c • v) = c • blockHad k v := by
  funext su; simp [blockHad_apply, Finset.mul_sum, mul_left_comm]

lemma blockHad_zero : blockHad k (0 : β × Idx k → ℤ) = 0 := by
  funext su; simp [blockHad_apply]

/-- The block Hadamard map as a `ℤ`-linear map. -/
def blockHadₗ : (β × Idx k → ℤ) →ₗ[ℤ] (β × Idx k → ℤ) where
  toFun := blockHad k
  map_add' := blockHad_add k
  map_smul' := blockHad_smul k

@[simp] lemma blockHadₗ_apply (v : β × Idx k → ℤ) : blockHadₗ k v = blockHad k v := rfl

/-- `H` applied twice is multiplication by `2^k`. -/
lemma blockHad_blockHad (v : β × Idx k → ℤ) : blockHad k (blockHad k v) = (2 ^ k : ℤ) • v := by
  funext su
  simp only [blockHad]
  rw [show (fun w => (whMat k).mulVec (fun w' => v (su.1, w')) w) =
      (whMat k).mulVec (fun w' => v (su.1, w')) from rfl]
  rw [Matrix.mulVec_mulVec, whMat_mul_whMat, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

/-- The inverse `2^{-k} H` of the block Hadamard map, on its image: `blockInv k (blockHad k u) = u`
(integer division is exact there). -/
def blockInv (v : β × Idx k → ℤ) : β × Idx k → ℤ := fun su => blockHad k v su / 2 ^ k

lemma blockInv_blockHad (u : β × Idx k → ℤ) : blockInv k (blockHad k u) = u := by
  funext su
  simp only [blockInv, blockHad_blockHad, Pi.smul_apply, smul_eq_mul]
  exact Int.mul_ediv_cancel_left (u su) (by positivity)

/-- Parseval's identity for the block Hadamard map. -/
lemma sum_sq_blockHad [Fintype β] (v : β × Idx k → ℤ) :
    ∑ su, (blockHad k v su) ^ 2 = 2 ^ k * ∑ su, (v su) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have := dotProduct_mulVec_self k (fun w => v (s, w))
  simp only [dotProduct, ← sq] at this
  exact this

/-- Entries of the block Hadamard map are bounded by the `ℓ_1` norm of the block. -/
lemma abs_blockHad_le (v : β × Idx k → ℤ) (su : β × Idx k) :
    |blockHad k v su| ≤ ∑ w, |v (su.1, w)| := by
  rw [blockHad_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp [abs_mul, abs_wh]

lemma blockHad_eq_zero_of_block (v : β × Idx k → ℤ) (su : β × Idx k)
    (h : ∀ w, v (su.1, w) = 0) : blockHad k v su = 0 := by
  simp [blockHad_apply, h]

end Block

end Hadamard

end LatticePrepro
