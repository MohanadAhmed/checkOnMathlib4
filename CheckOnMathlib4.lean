import Mathlib
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.SimpRw

variable (l m n: Type)
variable [Fintype l][Fintype m][Fintype n][DecidableEq m][DecidableEq n][DecidableEq l]


variable (R: Type)
variable [Field R][DecidableEq R]

namespace Matrix
open Matrix

/-- LDU decomposition of a block matrix with an invertible top-left corner, using the
Schur complement. -/
lemma from_blocks_eq_of_invertible₁₁
  (A : Matrix m m R) (B : Matrix m n R) (C : Matrix l m R) (D : Matrix l n R) [Invertible A] :
  fromBlocks A B C D = 
    fromBlocks 1 0 (C⬝⅟A) 1 ⬝ fromBlocks A 0 0 (D - C⬝(⅟A)⬝B) ⬝ fromBlocks 1 (⅟A⬝B) 0 1 := by
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.invOf_mul_self, Matrix.mul_invOf_self_assoc,
        Matrix.mul_invOf_mul_self_cancel, Matrix.mul_assoc, add_sub_cancel'_right]

/-- LDU decomposition of a block matrix with an invertible bottom-right corner, using the
Schur complement. -/
lemma from_blocks_eq_of_invertible₂₂
  (A : Matrix l m R) (B : Matrix l n R) (C : Matrix n m R) (D : Matrix n n R) [Invertible D] :
  fromBlocks A B C D =
    fromBlocks 1 (B⬝⅟D) 0 1 ⬝ fromBlocks (A - B⬝⅟D⬝C) 0 0 D ⬝ fromBlocks 1 0 (⅟D ⬝ C) 1 := by
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_invOf_self_assoc, 
        Matrix.mul_invOf_mul_self_cancel, Matrix.mul_assoc, sub_add_cancel, Matrix.invOf_mul_self]

section det

lemma det_from_blocks₁₁ (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R) (D : Matrix n n R)
  [Invertible A] : (Matrix.fromBlocks A B C D).det = det A * det (D - C ⬝ (⅟A) ⬝ B) := by
  rw [from_blocks_eq_of_invertible₁₁, det_mul, det_mul, det_fromBlocks_zero₂₁,
    det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, det_one, one_mul, one_mul, mul_one]

@[simp] lemma det_from_blocks_one₁₁ (B : Matrix m n R) (C : Matrix n m R) (D : Matrix n n R) :
  (Matrix.fromBlocks 1 B C D).det = det (D - C ⬝ B) := by
  haveI : Invertible (1 : Matrix m m R) := invertibleOne
  rw [det_from_blocks₁₁, invOf_one, Matrix.mul_one, det_one, one_mul]

/-- Determinant of a 2×2 block matrix, expanded around an invertible bottom right element in terms
of the Schur complement. -/
lemma det_from_blocks₂₂ (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R) (D : Matrix n n R)
  [Invertible D] : (Matrix.fromBlocks A B C D).det = det D * det (A - B ⬝ (⅟D) ⬝ C) := by
  have : fromBlocks A B C D = (fromBlocks D C B A).submatrix (Equiv.sumComm _ _) (Equiv.sumComm _ _) := by
    ext i j
    cases i;cases j; rfl; rfl
    cases j; rfl; rfl
  rw [this, Matrix.det_submatrix_equiv_self, det_from_blocks₁₁]

@[simp] lemma det_from_blocks_one₂₂ (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R):
  (Matrix.fromBlocks A B C 1).det = det (A - B ⬝ C) := by
  haveI : Invertible (1 : Matrix n n R) := invertibleOne
  rw [det_from_blocks₂₂, invOf_one, Matrix.mul_one, det_one, one_mul]

lemma det_one_add_mul_comm(A : Matrix m n R) (B : Matrix n m R) :
  Matrix.det (1 + A ⬝ B) = Matrix.det (1 + B ⬝ A) := by
  calc  det (1 + A ⬝ B) 
        = det (fromBlocks 1 (-A) B 1) := by rw [det_from_blocks_one₂₂, Matrix.neg_mul, sub_neg_eq_add]
     _  = det (1 + B ⬝ A)              := by rw [det_from_blocks_one₁₁, Matrix.mul_neg, sub_neg_eq_add]

lemma MatrixDeterminantLemma
  (A: Matrix m m R)(U: Matrix m n R)(V: Matrix n m R)(hA: IsUnit A.det):
  (A + U⬝V).det = A.det*(1 + V⬝(A⁻¹)⬝U).det := by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (U⬝V), ←Matrix.mul_add, det_mul,
    ←Matrix.mul_assoc, det_one_add_mul_comm, ←Matrix.mul_assoc]
  
end det

section is_R_or_C

scoped infixl:65 " ⊕ᵥ " => Sum.elim

variable (𝕜 : Type) [IsROrC 𝕜]

lemma schur_complement_eq₁₁ [Fintype m] [DecidableEq m] [Fintype n]
  {A : Matrix m m 𝕜} (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) (x : m → 𝕜) (y : n → 𝕜)
  [Invertible A] (hA : A.IsHermitian) :
vecMul (star (x ⊕ᵥ y)) (fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
  vecMul (star (x + (A⁻¹ ⬝ B).mulVec y)) A ⬝ᵥ (x + (A⁻¹ ⬝ B).mulVec y) +
    vecMul (star y) (D - Bᴴ ⬝ A⁻¹ ⬝ B) ⬝ᵥ y := by
  have hi := isUnit_det_of_invertible A
  simp_rw [star_add, add_vecMul, vecMul_add, add_dotProduct, dotProduct_add, vecMul_sub, 
    sub_dotProduct, star_mulVec, conjTranspose_mul, hA.inv.eq, conjTranspose_conjTranspose, 
    dotProduct_mulVec, vecMul_vecMul,
    nonsing_inv_mul_cancel_right _ _ hi, mul_nonsing_inv_cancel_left _ _ hi, 
    ← Matrix.mul_assoc, ← add_sub_assoc]
  simp_rw [Function.star_sum_elim, vecMul_fromBlocks, fromBlocks_mulVec, dotProduct_block, 
    star_add, add_dotProduct, dotProduct_add, Sum.elim_comp_inl, Sum.elim_comp_inr, add_dotProduct]
  abel

lemma schur_complement_eq₂₂ [Fintype m] [Fintype n] [DecidableEq n]
  (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) {D : Matrix n n 𝕜} (x : m → 𝕜) (y : n → 𝕜)
  [Invertible D] (hD : D.IsHermitian) :
vecMul (star (x ⊕ᵥ y)) (fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
  vecMul (star ((D⁻¹ ⬝ Bᴴ).mulVec x + y)) D ⬝ᵥ ((D⁻¹ ⬝ Bᴴ).mulVec x + y) +
    vecMul (star x) (A - B ⬝ D⁻¹ ⬝ Bᴴ) ⬝ᵥ x := by
  have hi := isUnit_det_of_invertible D
  simp_rw [star_add, add_vecMul, vecMul_add, add_dotProduct, dotProduct_add, vecMul_sub, 
    sub_dotProduct, star_mulVec, conjTranspose_mul, hD.inv.eq, conjTranspose_conjTranspose, 
    dotProduct_mulVec, vecMul_vecMul,
    nonsing_inv_mul_cancel_right _ _ hi, mul_nonsing_inv_cancel_left _ _ hi, 
    ← Matrix.mul_assoc, ← add_sub_assoc]
  simp_rw [Function.star_sum_elim, vecMul_fromBlocks, fromBlocks_mulVec, dotProduct_block, 
    star_add, add_dotProduct, dotProduct_add, Sum.elim_comp_inl, Sum.elim_comp_inr, add_dotProduct]
  abel

lemma IsHermitian.from_blocks₁₁ [Fintype m] [DecidableEq m]
  {A : Matrix m m 𝕜} (B : Matrix m n 𝕜) (D : Matrix n n 𝕜)
  (hA : A.IsHermitian) :
  (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).IsHermitian := by
  simp_rw [ Matrix.isHermitian_fromBlocks_iff, IsHermitian, Matrix.conjTranspose_sub, 
    conjTranspose_mul, conjTranspose_conjTranspose, hA.inv.eq, Matrix.mul_assoc, sub_left_inj,
    eq_self_iff_true, hA.eq, true_and]

lemma IsHermitian.from_blocks₂₂ [Fintype n] [DecidableEq n]
  (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) {D : Matrix n n 𝕜}
  (hD : D.IsHermitian) :
  (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).IsHermitian := by
  simp_rw [ Matrix.isHermitian_fromBlocks_iff, IsHermitian, Matrix.conjTranspose_sub, 
    conjTranspose_mul, conjTranspose_conjTranspose, hD.inv.eq, Matrix.mul_assoc, sub_left_inj,
    eq_self_iff_true, hD.eq, and_true]

/- lemma pos_semidef.from_blocks₁₁ [Fintype m] [DecidableEq m] [Fintype n]
  {A : Matrix m m 𝕜} (B : Matrix m n 𝕜) (D : Matrix n n 𝕜)
  (hA : A.posDef) [Invertible A] :
  (from_blocks A B Bᴴ D).pos_semidef ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).pos_semidef := sorry -/
/- begin
  rw [pos_semidef, is_hermitian.from_blocks₁₁ _ _ hA.1],
  split,
  { refine λ h, ⟨h.1, λ x, _⟩,
    have := h.2 (- ((A⁻¹ ⬝ B).mul_vec x) ⊕ᵥ x),
    rw [dot_product_mul_vec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_self,
      dot_product_zero, zero_add] at this,
    rw [dot_product_mul_vec], exact this },
  { refine λ h, ⟨h.1, λ x, _⟩,
    rw [dot_product_mul_vec, ← sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1,
      map_add],
    apply le_add_of_nonneg_of_le,
    { rw ← dot_product_mul_vec,
      apply hA.pos_semidef.2, },
    { rw ← dot_product_mul_vec, apply h.2 } }
end -/

/- lemma pos_semidef.from_blocks₂₂ [Fintype m] [Fintype n] [DecidableEq n]
  (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) {D : Matrix n n 𝕜}
  (hD : D.pos_def) [Invertible D] :
  (fromBlocks A B Bᴴ D).pos_semidef ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).pos_semidef := sorry -/
/- begin
  rw [←pos_semidef_submatrix_equiv (equiv.sum_comm n m), equiv.sum_comm_apply,
    from_blocks_submatrix_sum_swap_sum_swap],
  convert pos_semidef.from_blocks₁₁ _ _ hD; apply_instance <|> simp
end -/

end is_R_or_C

