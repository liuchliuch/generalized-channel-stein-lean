import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Transposition preserves the Hilbert operator norm

The norm in this file is the L2 operator norm supplied by
`Matrix.Norms.L2Operator`. Ordinary transpose preserves this norm for arbitrary
rectangular complex matrices, including matrices with an empty index type.
-/

noncomputable section
namespace QuantumChannelStein.TransposeNorm

open scoped Matrix.Norms.L2Operator
open Matrix WithLp

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Coordinatewise complex conjugation of a Euclidean vector. -/
def conjugate (x : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  toLp 2 (fun i => star (x i))

/-- Complex conjugation is an isometry for the Euclidean norm. -/
@[simp] theorem conjugate_norm (x : EuclideanSpace ℂ n) :
    ‖conjugate x‖ = ‖x‖ := by
  simp [EuclideanSpace.norm_eq, conjugate]

omit [Fintype m] in
/-- Entrywise conjugation intertwines matrix action with vector conjugation. -/
theorem map_star_mulVec (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    toLp 2 (A.map star *ᵥ ofLp x) =
      conjugate (toLp 2 (A *ᵥ ofLp (conjugate x))) := by
  ext i
  simp [conjugate, Matrix.mulVec, dotProduct, mul_comm]

variable [DecidableEq n]

/-- Entrywise complex conjugation does not increase the L2 operator norm. -/
theorem opNorm_map_star_le (A : Matrix m n ℂ) : ‖A.map star‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  change ‖toLp 2 (A.map star *ᵥ ofLp x)‖ ≤ ‖A‖ * ‖x‖
  rw [map_star_mulVec, conjugate_norm]
  simpa only [conjugate_norm] using Matrix.l2_opNorm_mulVec A (conjugate x)

/-- Entrywise complex conjugation preserves the L2 operator norm. -/
@[simp] theorem opNorm_map_star (A : Matrix m n ℂ) : ‖A.map star‖ = ‖A‖ := by
  apply le_antisymm (opNorm_map_star_le A)
  simpa only [Matrix.map_map, star_star, Function.comp_def, Matrix.map_id] using
    opNorm_map_star_le (A.map star)

variable [DecidableEq m]

/-- Ordinary transpose preserves the L2 operator norm, including in zero dimensions. -/
@[simp] theorem opNorm_transpose (A : Matrix m n ℂ) : ‖Aᵀ‖ = ‖A‖ := by
  calc
    ‖Aᵀ‖ = ‖Aᴴ.map star‖ := by congr 1; ext i j; simp
    _ = ‖Aᴴ‖ := opNorm_map_star _
    _ = ‖A‖ := Matrix.l2_opNorm_conjTranspose A

end QuantumChannelStein.TransposeNorm
