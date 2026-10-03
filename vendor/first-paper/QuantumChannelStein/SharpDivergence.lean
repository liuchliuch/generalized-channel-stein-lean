import QuantumChannelStein.SupportedGeometricMean
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-! # Literal supported geometric-mean divergence optimization
This is an auxiliary finite-dimensional optimization for the adaptive chain
rule. The geometric mean is used with explicit support constraints, not an
unjustified unrestricted Moore–Penrose formula. Equivalence to any broader
optimization and regularization identities are separate proof obligations.
-/
noncomputable section
namespace QuantumChannelStein.SharpDivergence
open Matrix SupportedGeometricMean
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] SandwichedRenyi.matrixCStar
variable {n : ℕ}

/-- An actual positive auxiliary matrix feasible for the supported mean program. -/
structure Feasible (p : ℝ) (A B : Operator n) (hB : B.PosSemidef) where
  matrix : Operator n
  positive : matrix.PosSemidef
  supported : LinearMap.ker B.mulVecLin ≤ LinearMap.ker matrix.mulVecLin
  dominates : A ≤ mean p B hB matrix

/-- Infimum of actual traces of feasible auxiliary matrices; empty infimum is infinity. -/
def quasi (p : ℝ) (A B : Operator n) (hB : B.PosSemidef) : ENNReal :=
  ⨅ X : Feasible p A B hB, ENNReal.ofReal X.matrix.trace.re

/-- Base-two state divergence associated with the literal geometric-mean program. -/
def divergence (α : ℝ) (_hα : 1 < α) (ρ σ : State n) : EReal :=
  (((α - 1) * Real.log 2)⁻¹ : ℝ) * ENNReal.log (quasi (1 / α) ρ.matrix σ.matrix σ.positive)

theorem quasi_le_trace {p : ℝ} {A B : Operator n} {hB : B.PosSemidef}
    (X : Feasible p A B hB) : quasi p A B hB ≤ ENNReal.ofReal X.matrix.trace.re :=
  iInf_le _ X

/-- A smaller numerator has a larger feasible set. -/
theorem quasi_mono_first (p : ℝ) (A C B : Operator n) (hB : B.PosSemidef)
    (hAC : A ≤ C) : quasi p A B hB ≤ quasi p C B hB := by
  apply le_iInf
  intro X
  exact quasi_le_trace ⟨X.matrix, X.positive, X.supported, hAC.trans X.dominates⟩

/-- The zero auxiliary matrix is feasible for zero numerator for every positive order. -/
def zeroFeasible (p : ℝ) (hp : 0 < p) (B : Operator n) (hB : B.PosSemidef) :
    Feasible p 0 B hB where
  matrix := 0
  positive := Matrix.PosSemidef.zero
  supported := by simp
  dominates := by
    exact (mean_positive p B hB 0).nonneg

theorem quasi_zero (p : ℝ) (hp : 0 < p) (B : Operator n) (hB : B.PosSemidef) :
    quasi p 0 B hB = 0 := by
  apply le_antisymm _ bot_le
  simpa [zeroFeasible] using quasi_le_trace (zeroFeasible p hp B hB)

end QuantumChannelStein.SharpDivergence
