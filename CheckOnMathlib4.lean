import Mathlib
import Mathlib.Tactic.NthRewrite

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

end is_R_or_C