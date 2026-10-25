import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef

 





set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]
  (A : Matrix m m ℝ) (B : Matrix m n ℝ)
  (C : Matrix n m ℝ) (D : Matrix n n ℝ)

 


theorem dgff_schur_factorization [Invertible A] :
    fromBlocks A B C D =
      fromBlocks 1 0 (C * ⅟A) 1 *
        fromBlocks A 0 0 (D - C * ⅟A * B) *
        fromBlocks 1 (⅟A * B) 0 1 :=
  Matrix.fromBlocks_eq_of_invertible₁₁ A B C D

 

theorem dgff_schur_cross_zero [Invertible A]
    [Invertible (D - C * ⅟A * B)]
    [Invertible (fromBlocks A B C D)] :
    (⅟(fromBlocks A B C D)).toBlocks₁₂ +
      ⅟A * B * (⅟(fromBlocks A B C D)).toBlocks₂₂ = 0 := by
  rw [Matrix.invOf_fromBlocks₁₁_eq A B C D]
  simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂]
  simp

 

theorem dgff_schur_inner_covariance [Invertible A]
    [Invertible (D - C * ⅟A * B)]
    [Invertible (fromBlocks A B C D)] :
    (⅟(fromBlocks A B C D)).toBlocks₁₁ +
      ⅟A * B * (⅟(fromBlocks A B C D)).toBlocks₂₁ = ⅟A := by
  rw [Matrix.invOf_fromBlocks₁₁_eq A B C D]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁]
  simp [Matrix.mul_assoc]

end SupercriticalLQGUniqueness.B2.QPos
