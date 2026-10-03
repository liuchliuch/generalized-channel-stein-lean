import QuantumChannelStein.SharpDivergence
import QuantumChannelStein.GeometricMeanKraus

/-! # Actual channel data processing of the supported mean program
Every feasible matrix is pushed through the real Kraus action. The objective
trace is preserved, so the infimum and its extended logarithm decrease.
-/
noncomputable section
namespace QuantumChannelStein.SharpDivergence
open Matrix SupportedGeometricMean
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] SandwichedRenyi.matrixCStar
variable {n m : ℕ}

def Feasible.map {p : ℝ} (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    {A B : Operator n} {hB : B.PosSemidef} (X : Feasible p A B hB)
    (Φ : KrausChannel n m) : Feasible p (Φ.apply A) (Φ.apply B) (Φ.apply_positive hB) where
  matrix := Φ.apply X.matrix
  positive := Φ.apply_positive X.positive
  supported := krausSum_support Finset.univ Φ.kraus X.matrix B X.positive hB X.supported
  dominates := by
    have hh := Φ.apply_positive (sub_nonneg.mpr X.dominates).posSemidef
    have hm : Φ.apply A ≤ Φ.apply (mean p B hB X.matrix) := by
      apply sub_nonneg.mp
      have heq : Φ.apply (mean p B hB X.matrix - A) =
          Φ.apply (mean p B hB X.matrix) - Φ.apply A :=
        map_sub Φ.toLinearMap _ _
      rw [heq] at hh
      exact hh.nonneg
    exact hm.trans (channel_transformer p hp Φ X.matrix B X.positive hB X.supported)

theorem quasi_data_processing (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (Φ : KrausChannel n m) (A B : Operator n) (hB : B.PosSemidef) :
    quasi p (Φ.apply A) (Φ.apply B) (Φ.apply_positive hB) ≤ quasi p A B hB := by
  apply le_iInf
  intro X
  have h := quasi_le_trace (X.map hp Φ)
  simpa only [Feasible.map, KrausChannel.trace_apply] using h

theorem divergence_data_processing (α : ℝ) (hα : 1 < α)
    (Φ : KrausChannel n m) (ρ σ : State n) :
    divergence α hα (Φ.onState ρ) (Φ.onState σ) ≤ divergence α hα ρ σ := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hp : 1 / α ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨one_div_pos.mpr hα0, (div_le_one hα0).mpr hα.le⟩
  apply mul_le_mul_of_nonneg_left
    (ENNReal.log_le_log (quasi_data_processing (1 / α) hp Φ ρ.matrix σ.matrix σ.positive))
  apply EReal.coe_nonneg.mpr
  exact inv_nonneg.mpr (mul_nonneg (sub_nonneg.mpr hα.le)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))

end QuantumChannelStein.SharpDivergence
