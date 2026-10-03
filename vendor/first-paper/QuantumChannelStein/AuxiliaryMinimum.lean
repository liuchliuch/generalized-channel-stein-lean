import QuantumChannelStein.EnvironmentTensor
import Mathlib.Topology.Order.Compact

/-! # Attainment of the fixed-environment auxiliary minimum -/
noncomputable section
namespace QuantumChannelStein
open scoped Matrix.Norms.L2Operator Kronecker

theorem exists_minimizing_auxiliary {a b eN eM : ℕ}
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (t : ℝ) :
    ∃ C : Matrix (Fin eN) (Fin eM) ℂ, ‖C‖ ≤ Real.sqrt t ∧
      ∀ D : Matrix (Fin eN) (Fin eM) ℂ, ‖D‖ ≤ Real.sqrt t →
        ‖VN - ((1 : Operator b) ⊗ₖ C) * VM‖ ≤
          ‖VN - ((1 : Operator b) ⊗ₖ D) * VM‖ := by
  let f : Matrix (Fin eN) (Fin eM) ℂ → ℝ :=
    fun C => ‖VN - EnvironmentTensor.environmentLinear VM C‖
  have hf : Continuous f :=
    (continuous_const.sub (EnvironmentTensor.environmentLinear VM).continuous_of_finiteDimensional).norm
  obtain ⟨C, hC, hmin⟩ := (isCompact_closedBall (0 : Matrix (Fin eN) (Fin eM) ℂ)
    (Real.sqrt t)).exists_isMinOn ⟨0, by simp⟩ hf.continuousOn
  refine ⟨C, by simpa using hC, ?_⟩
  intro D hD
  exact hmin (by simpa using hD)
end QuantumChannelStein
