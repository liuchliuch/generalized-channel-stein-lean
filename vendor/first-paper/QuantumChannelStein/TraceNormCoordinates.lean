import QuantumChannelStein.DiamondNormChannel
import QuantumChannelStein.MatrixBlockCalculus
import QuantumChannelStein.SharpTensorTransport
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-! # Exact trace-norm coordinate, scalar and Hermitian-dilation identities -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.TraceNorm
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
local instance traceNormCoordinateCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
local instance traceNormCoordinateCStar2 : CStarAlgebra (Matrix κ κ ℂ) := CStarAlgebra.mk
local instance traceNormCoordinateCStar3 : CStarAlgebra (Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) := CStarAlgebra.mk

/-- The installed library and local norm are literally the same trace-square-root definition. -/
theorem traceNorm_eq_matrixTraceNorm (A : Matrix ι ι ℂ) : traceNorm A = Matrix.traceNorm A := rfl

theorem traceNorm_smul (c : ℂ) (A : Matrix ι ι ℂ) : traceNorm (c • A) = ‖c‖ * traceNorm A :=
  Matrix.traceNorm_smul A c

theorem traceNorm_real_smul (c : ℝ) (A : Matrix ι ι ℂ) : traceNorm (c • A) = |c| * traceNorm A := by
  rw [show c • A = (c : ℂ) • A by ext i j; simp [Complex.real_smul], traceNorm_smul]
  simp

theorem traceNorm_conjTranspose (A : Matrix ι ι ℂ) : traceNorm Aᴴ = traceNorm A :=
  Matrix.traceNorm_conjTranspose A

theorem traceNorm_reindex (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    traceNorm (Matrix.reindex e e A) = traceNorm A := by
  unfold traceNorm
  rw [Matrix.conjTranspose_reindex, ← SupportedGeometricMean.reindex_mul]
  rw [CFC.sqrt_eq_rpow, CFC.sqrt_eq_rpow, ← CFC.rpow_eq_pow,
    SandwichedRenyi.rpow_reindex e _ A.posSemidef_conjTranspose_mul_self]
  rw [ChannelEntropy.trace_reindex_equiv, CFC.rpow_eq_pow]

def hermitianDilation (A : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks 0 A Aᴴ 0

theorem hermitianDilation_isHermitian (A : Matrix ι ι ℂ) : (hermitianDilation A).IsHermitian := by
  change (hermitianDilation A)ᴴ = hermitianDilation A
  simp [hermitianDilation, Matrix.fromBlocks_conjTranspose]

/-- Hermitian block dilation doubles exactly the genuine trace norm. -/
theorem traceNorm_hermitianDilation (A : Matrix ι ι ℂ) :
    traceNorm (hermitianDilation A) = 2 * traceNorm A := by
  have hAA : (A * Aᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using Aᴴ.posSemidef_conjTranspose_mul_self
  have hA : (Aᴴ * A).PosSemidef := A.posSemidef_conjTranspose_mul_self
  unfold traceNorm hermitianDilation
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_conjTranspose, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, zero_add, add_zero]
  rw [CFC.sqrt_eq_rpow, ← CFC.rpow_eq_pow, MatrixBlockCalculus.rpow_fromBlocks _ _ hAA hA]
  have htr (M N : Matrix ι ι ℂ) : (Matrix.fromBlocks M 0 0 N).trace = M.trace + N.trace := by
    simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  rw [htr, Complex.add_re]

  have h := traceNorm_conjTranspose A
  unfold traceNorm at h
  rw [Matrix.conjTranspose_conjTranspose] at h
  simp only [CFC.sqrt_eq_rpow, ← CFC.rpow_eq_pow] at h ⊢
  linarith

/-- Finite trace-norm subadditivity on the actual matrix sum. -/
theorem traceNorm_sum_le {η : Type*} (s : Finset η) (A : η → Matrix ι ι ℂ) :
    traceNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, traceNorm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

end QuantumChannelStein.TraceNorm
