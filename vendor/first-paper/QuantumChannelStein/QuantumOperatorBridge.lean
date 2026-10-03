import QuantumChannelStein.MatrixOperatorBridge
import Quantum.QuantumMechanics.QuantumChannel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-! CFC transport into the concrete Hilbert-space operators of Lean-Quantum. -/
noncomputable section
namespace QuantumChannelStein.MatrixOperatorBridge
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : ℕ}

local instance operatorCStar : CStarAlgebra (H n →ₗ[ℂ] H n) :=
  QuantumChannel.instCStarAlgebraL (H n)

local instance operatorStar : Star (H n →ₗ[ℂ] H n) :=
  (operatorCStar (n := n)).toStar

local instance operatorStarRing : StarRing (H n →ₗ[ℂ] H n) :=
  (operatorCStar (n := n)).toStarRing

set_option backward.isDefEq.respectTransparency false

theorem op_cfc (A : M n) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    opEquiv n (cfc f A) = cfc f (opEquiv n A) := by
  exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ)
    (A := M n) (B := H n →ₗ[ℂ] H n) (φ := opEquiv n) (f := f) (a := A)
    (hf := A.finite_real_spectrum.continuousOn f)
    (hφ := (opEquiv n).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional)
    (ha := hA.isSelfAdjoint)
    (hφa := hA.isSelfAdjoint.map (opEquiv n))

theorem op_log (A : M n) (hA : A.IsHermitian) :
    opEquiv n (cfc Real.log A) = CFC.log (opEquiv n A) := by
  exact op_cfc A hA Real.log

end QuantumChannelStein.MatrixOperatorBridge
