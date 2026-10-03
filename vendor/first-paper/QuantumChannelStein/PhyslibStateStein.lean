import QuantumChannelStein.PhyslibTensorBridge
import QuantumChannelStein.SupportedStateStein

/-! Ordinary supported-state direct Stein theorem in the channel project's
literal density matrices, tensor coordinates, effects, and base-two units. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.PhyslibStateBridge
open Matrix TensorPower RelativeEntropy Filter
open scoped BigOperators ComplexOrder Topology

/-- No asymptotic premise remains: this is the supported direct state theorem
proved from the checked generalized Stein source and the exact faithful fill. -/
theorem supported_state_direct (d : ℕ) (rho sigma : State d)
    (hs : supportIncluded rho sigma) (epsilon : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : (u : EReal) < umegaki rho sigma) :
    ∀ᶠ m : ℕ in atTop,
      ∃ T : Matrix (Index (Fin d) m) (Index (Fin d) m) ℂ,
        T.PosSemidef ∧ (1 - T).PosSemidef ∧
        (tensorPower rho.matrix m * (1 - T)).trace.re ≤ epsilon ∧
        (tensorPower sigma.matrix m * T).trace.re ≤ (2 : ℝ) ^ (-(m : ℝ) * u) := by
  let eps : Prob := ⟨epsilon, hepsilon0.le, hepsilon1.le⟩
  have heps : 0 < eps ∧ eps < 1 := ⟨hepsilon0, hepsilon1⟩
  have hu' : u < (qRelativeEnt (toMState rho) (toMState sigma)).toReal / Real.log 2 := by
    rw [entropy_toReal_base_two rho sigma hs]
    rw [umegaki_of_supportIncluded rho sigma hs] at hu
    exact_mod_cast hu
  filter_upwards [StateSteinAudit.supported_state_stein_direct_base_two
    (toMState rho) (toMState sigma) (support_toMState hs) heps hu0 hu'] with m hm
  obtain ⟨T, hT0, hT1, herr, hq⟩ := hm
  let e := (tupleEquiv (Fin d) m).symm
  let U := Matrix.reindex e e T.mat
  have hU : U.PosSemidef := (HermitianMat.zero_le_iff.mp hT0).submatrix e.symm
  have hc : (1 - U).PosSemidef := by
    have h := (HermitianMat.zero_le_iff.mp (sub_nonneg.mpr hT1)).submatrix e.symm
    change (Matrix.reindexLinearEquiv ℂ ℂ e e (1 - T.mat)).PosSemidef at h
    rwa [map_sub, Matrix.reindexLinearEquiv_one] at h
  refine ⟨U, hU, hc, ?_, ?_⟩
  · rw [npow_exp_val_eq] at herr
    change (tensorPower rho.matrix m *
      (Matrix.reindexLinearEquiv ℂ ℂ e e (1 - T.mat))).trace.re ≤ epsilon at herr
    rwa [map_sub, Matrix.reindexLinearEquiv_one] at herr
  · exact (npow_exp_val_eq sigma m T) ▸ hq

end QuantumChannelStein.PhyslibStateBridge

namespace QuantumChannelStein.ParallelSteinAssembly

/-- The ordinary state-Stein premise is discharged by the concrete checked theorem. -/
theorem supportedStateDirect : SupportedStateDirect :=
  PhyslibStateBridge.supported_state_direct

end QuantumChannelStein.ParallelSteinAssembly
