import QuantumChannelStein.SharpFeasibleTransport
import QuantumChannelStein.FaithfulMarginalMinimax
import QuantumChannelStein.GeometricMeanTensor
import QuantumChannelStein.DivergenceOptimization

/-! # Faithful weighted-Choi coordinates and the exact marginal objective -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SharpChannel
open Matrix Pseudoinverse FaithfulDensity ChannelEntropy
open scoped BigOperators Kronecker MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {a b : ℕ}

def flatten (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : Operator (a*b) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv X

def unflatten (X : Operator (a*b)) : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm X

@[simp] theorem flatten_unflatten (X : Operator (a*b)) : flatten (unflatten X) = X := by
  ext i j; simp only [flatten, unflatten, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

@[simp] theorem unflatten_flatten (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : unflatten (flatten X) = X := by
  ext i j; simp only [flatten, unflatten, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem flatten_mul (X Y : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    flatten (X * Y) = flatten X * flatten Y :=
  (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv).map_mul X Y

theorem flatten_adjoint (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    flatten Xᴴ = (flatten X)ᴴ := (Matrix.conjTranspose_reindex _ _ _).symm

@[simp] theorem flatten_one : flatten (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) = 1 :=
  (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv).map_one

def marginalLinear (a b : ℕ) : Operator (a*b) →ₗ[ℝ] Operator a where
  toFun X := KrausChannel.traceOutput (unflatten X)
  map_add' X Y := by ext i j; simp [unflatten, KrausChannel.traceOutput, Matrix.reindex_apply, Matrix.submatrix_apply, Finset.sum_add_distrib]
  map_smul' c X := by ext i j; simp [unflatten, KrausChannel.traceOutput, Matrix.reindex_apply, Matrix.submatrix_apply, Finset.mul_sum]

theorem marginal_positive (X : Operator (a*b)) (hX : X.PosSemidef) : (marginalLinear a b X).PosSemidef :=
  TestingSDP.traceOutput_positive (hX.submatrix finProdFinEquiv)

def weight (omega : State a) (b : ℕ) : Operator (a*b) := flatten (root omega.matrix omega.positive ⊗ₖ (1 : Operator b))
def inverseWeight (omega : State a) (b : ℕ) : Operator (a*b) := flatten (inverseSqrt omega.matrix omega.positive ⊗ₖ (1 : Operator b))

theorem weight_inverseWeight (omega : State a) (h : omega.matrix.PosDef) (b : ℕ) :
    weight omega b * inverseWeight omega b = 1 := by
  rw [weight, inverseWeight, ← flatten_mul, ← Matrix.mul_kronecker_mul,
    root_inverseSqrt omega.matrix h]
  simp

theorem inverseWeight_weight (omega : State a) (h : omega.matrix.PosDef) (b : ℕ) :
    inverseWeight omega b * weight omega b = 1 := by
  rw [weight, inverseWeight, ← flatten_mul, ← Matrix.mul_kronecker_mul,
    inverseSqrt_root omega.matrix h]
  simp

theorem weight_trace (omega : State a) (X : Operator (a*b)) :
    (weight omega b * X * (weight omega b)ᴴ).trace = (marginalLinear a b X * omega.matrix).trace := by
  let S := root omega.matrix omega.positive ⊗ₖ (1 : Operator b)
  have hS : Sᴴ * S = omega.matrix ⊗ₖ (1 : Operator b) := by
    simp only [S, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      (root_isHermitian omega.matrix omega.positive).eq, ← Matrix.mul_kronecker_mul,
      root_mul_root, Matrix.one_mul]
  calc
    _ = (flatten (S * unflatten X * Sᴴ)).trace := by
      rw [flatten_mul, flatten_mul, flatten_adjoint, flatten_unflatten]; rfl
    _ = (S * unflatten X * Sᴴ).trace := trace_reindex_equiv _ _
    _ = (unflatten X * (Sᴴ * S)).trace := by rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    _ = _ := by rw [hS]; exact TestingSDP.traceOutput_pairing omega.matrix (unflatten X)

theorem canonical_output_weight (Φ : KrausChannel a b) (omega : State a) :
    (ChannelEntropy.pureOutput Φ (TestingPrimal.densityInput omega)).matrix =
      weight omega b * flatten Φ.choi * (weight omega b)ᴴ := by
  rw [DivergenceOptimization.canonical_output_matrix]
  have hroot : root omega.matrix omega.positive = CFC.sqrt omega.matrix := by
    rw [SupportedGeometricMean.root_eq_rpow_half, CFC.rpow_eq_pow, CFC.sqrt_eq_rpow]
  rw [weight, hroot, ← flatten_adjoint, ← flatten_mul, ← flatten_mul]
  rfl

end QuantumChannelStein.SharpChannel
