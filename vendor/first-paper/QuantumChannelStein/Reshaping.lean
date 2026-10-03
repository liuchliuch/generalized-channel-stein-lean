import QuantumChannelStein.Stinespring
import QuantumChannelStein.Choi
import QuantumChannelStein.TensorNorm
import QuantumChannelStein.TransposeNorm

/-!
# Fixed-environment reshaping

The exact matrix identities behind equation (3.1) and Corollary 3.3. All
transposes here are ordinary transposes, not adjoints.
-/
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder Kronecker Matrix.Norms.L2Operator
open Matrix

/-- Rearrange a dilation's environment coordinate into vectorized Kraus columns. -/
def dilationColumns {a b e : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) :
    Matrix (Fin a × Fin b) (Fin e) ℂ := fun x k => V (x.2, k) x.1

/-- Reshaping is injective; no dilation normalization is required. -/
theorem dilationColumns_injective {a b e : ℕ} :
    Function.Injective (@dilationColumns a b e) := by
  intro V W h
  ext ⟨j, k⟩ i
  exact congrFun (congrFun h (i, j)) k

/-- The partial trace of the column Gram matrix is the transpose of `VᴴV`,
the exact algebraic identity in equation (3.1). -/
theorem traceOutput_columns_gram {a b e : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) :
    KrausChannel.traceOutput (dilationColumns V * (dilationColumns V)ᴴ) =
      (Vᴴ * V)ᵀ := by
  ext i j
  simp only [KrausChannel.traceOutput, dilationColumns, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

/-- An environment operation acts on Kraus columns by the ordinary transpose. -/
theorem dilationColumns_environment {a b e f : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (C : Matrix (Fin f) (Fin e) ℂ) :
    dilationColumns (((1 : Operator b) ⊗ₖ C) * V) = dilationColumns V * Cᵀ := by
  ext ⟨i, j⟩ k
  simp [dilationColumns, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_comm]

/-- A column factorization yields an exact environmental comparison on the
same prescribed environment spaces. -/
theorem environmental_comparison_of_columns {a b e f : ℕ}
    (VN : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (D : Matrix (Fin f) (Fin e) ℂ)
    (hD : dilationColumns VN = dilationColumns VM * D) :
    VN = ((1 : Operator b) ⊗ₖ Dᵀ) * VM := by
  apply dilationColumns_injective
  rw [dilationColumns_environment, Matrix.transpose_transpose]
  exact hD


/-- The norm identity in equation (3.1), using the actual L2 operator norm. -/
theorem norm_traceOutput_columns_gram {a b e : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) :
    ‖KrausChannel.traceOutput (dilationColumns V * (dilationColumns V)ᴴ)‖ = ‖V‖ ^ 2 := by
  rw [traceOutput_columns_gram, TransposeNorm.opNorm_transpose,
    Matrix.l2_opNorm_conjTranspose_mul_self, pow_two]

end QuantumChannelStein

