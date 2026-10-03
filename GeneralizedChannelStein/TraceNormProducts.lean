import QuantumChannelStein.TraceNormCoordinates
import QuantumChannelStein.TensorMap

/-! Exact trace-norm products for arbitrary complex matrices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem sqrt_kronecker_positive (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (A ⊗ₖ B)=CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  apply (CFC.sqrt_eq_iff _ _ (MatrixMap.posSemidef_kronecker hA hB).nonneg
    (MatrixMap.posSemidef_kronecker (CFC.sqrt_nonneg A).posSemidef (CFC.sqrt_nonneg B).posSemidef).nonneg).mpr
  rw [←Matrix.mul_kronecker_mul,CFC.sqrt_mul_sqrt_self A hA.nonneg,CFC.sqrt_mul_sqrt_self B hB.nonneg]

/-- Multiplicativity holds for all matrices, not only states or positive operators. -/
theorem traceNorm_kronecker (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    TraceNorm.traceNorm (A ⊗ₖ B)=TraceNorm.traceNorm A*TraceNorm.traceNorm B := by
  unfold TraceNorm.traceNorm
  rw [Matrix.conjTranspose_kronecker,←Matrix.mul_kronecker_mul,
    sqrt_kronecker_positive _ _ (Matrix.posSemidef_conjTranspose_mul_self A)
      (Matrix.posSemidef_conjTranspose_mul_self B),Matrix.trace_kronecker,Complex.mul_re]
  have ha := (Complex.nonneg_iff.mp (CFC.sqrt_nonneg (Aᴴ*A)).posSemidef.trace_nonneg).2
  have hb := (Complex.nonneg_iff.mp (CFC.sqrt_nonneg (Bᴴ*B)).posSemidef.trace_nonneg).2
  rw [←ha,←hb,mul_zero,sub_zero]

end GeneralizedChannelStein
