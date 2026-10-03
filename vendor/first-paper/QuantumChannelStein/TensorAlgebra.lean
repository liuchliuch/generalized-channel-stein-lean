import QuantumChannelStein.TensorNorm

/-!
# Tensor-product norm estimates

Operator bounds needed by the tensor amplification construction. The L2
operator norm instance is explicit throughout.
-/
noncomputable section
namespace QuantumChannelStein.TensorAlgebra
open scoped Kronecker Matrix.Norms.L2Operator
open Matrix

variable {m n r s : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq r] [DecidableEq s]

/-- The rectangular Hilbert operator norm is submultiplicative for Kronecker products. -/
theorem kronecker_opNorm_le (A : Matrix m n ℂ) (B : Matrix r s ℂ) :
    ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  have hfactor : A ⊗ₖ B =
      (A ⊗ₖ (1 : Matrix r r ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hfactor]
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul (TensorNorm.kronecker_one_opNorm_le A)
      (TensorNorm.one_kronecker_opNorm_le B) (norm_nonneg _) (norm_nonneg _))

/-- Tensoring a prescribed error with a contraction does not increase it. -/
theorem norm_kronecker_sub_le (A A' : Matrix m n ℂ) (B : Matrix r s ℂ)
    {error : ℝ} (herror : ‖A - A'‖ ≤ error) (hB : ‖B‖ ≤ 1) :
    ‖A ⊗ₖ B - A' ⊗ₖ B‖ ≤ error := by
  have hsub : A ⊗ₖ B - A' ⊗ₖ B = (A - A') ⊗ₖ B := by
    ext ⟨i,k⟩ ⟨j,l⟩
    simp [sub_mul]
  rw [hsub]
  calc
    ‖(A - A') ⊗ₖ B‖ ≤ ‖A - A'‖ * ‖B‖ := kronecker_opNorm_le _ _
    _ ≤ ‖A - A'‖ * 1 := mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ ≤ error := by simpa using herror

/-- A two-factor telescoping error estimate, the base step for tensor-power error control. -/
theorem kronecker_difference_le (A A' : Matrix m n ℂ) (B B' : Matrix r s ℂ) :
    ‖A ⊗ₖ B - A' ⊗ₖ B'‖ ≤ ‖A - A'‖ * ‖B‖ + ‖A'‖ * ‖B - B'‖ := by
  have hdecomp : A ⊗ₖ B - A' ⊗ₖ B' =
      (A - A') ⊗ₖ B + A' ⊗ₖ (B - B') := by
    ext ⟨i,k⟩ ⟨j,l⟩
    simp [sub_mul, mul_sub]
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add (kronecker_opNorm_le _ _) (kronecker_opNorm_le _ _))

end QuantumChannelStein.TensorAlgebra
