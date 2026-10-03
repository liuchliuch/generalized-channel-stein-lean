import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-! Matrix/operator coordinate identities for the isolated DPI bridge. -/
noncomputable section
namespace QuantumChannelStein.MatrixOperatorBridge
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

abbrev H (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev M (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def opEquiv (n : ℕ) : M n ≃⋆ₐ[ℂ] (H n →ₗ[ℂ] H n) :=
  (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Fin n) ℂ)).symm

@[simp] theorem opEquiv_apply {n : ℕ} (A : M n) :
    opEquiv n A = A.toEuclideanLin := rfl

theorem trace_op {n : ℕ} (A : M n) :
    LinearMap.trace ℂ (H n) (opEquiv n A) = A.trace := by
  exact Matrix.trace_toLin_eq A (EuclideanSpace.basisFun (Fin n) ℂ).toBasis

theorem op_nonneg_iff {n : ℕ} (A : M n) :
    0 ≤ opEquiv n A ↔ A.PosSemidef := by
  rw [LinearMap.nonneg_iff_isPositive, opEquiv_apply,
    Matrix.isPositive_toEuclideanLin_iff]

theorem ker_le_iff {n : ℕ} (A B : M n) :
    LinearMap.ker (opEquiv n B) ≤ LinearMap.ker (opEquiv n A) ↔
      LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  constructor
  · intro h x hx
    have hh := h (show WithLp.toLp 2 x ∈ LinearMap.ker (opEquiv n B) from by
      change WithLp.toLp 2 (B *ᵥ x) = 0
      have hb : B *ᵥ x = 0 := hx
      simp [hb])
    change A *ᵥ x = 0
    have ha : WithLp.toLp 2 (A *ᵥ x) = 0 := hh
    exact congrArg WithLp.ofLp ha
  · intro h x hx
    have hb : B *ᵥ WithLp.ofLp x = 0 := congrArg WithLp.ofLp hx
    have ha := h (show WithLp.ofLp x ∈ LinearMap.ker B.mulVecLin from hb)
    change WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) = 0
    change A *ᵥ WithLp.ofLp x = 0 at ha
    simp [ha]

theorem toEuclideanLin_mul {n m k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin k) ℂ) :
    (A * B).toEuclideanLin = A.toEuclideanLin.comp B.toEuclideanLin := by
  ext x i
  simp only [Matrix.toLpLin_apply, LinearMap.comp_apply,
    WithLp.ofLp_toLp, ← Matrix.mulVec_mulVec]

end QuantumChannelStein.MatrixOperatorBridge
