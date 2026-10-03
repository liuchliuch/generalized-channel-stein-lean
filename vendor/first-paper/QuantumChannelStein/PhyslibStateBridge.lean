import QuantumChannelStein.RelativeEntropy
import QuantumInfo.Entropy.Relative

/-! Finite density-matrix representation and entropy bridge to Physlib. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.PhyslibStateBridge
open Matrix
open scoped ComplexOrder

/-- The main density matrix regarded as the same Physlib density matrix. -/
def toMState {n : ℕ} (rho : State n) : MState (Fin n) where
  M := ⟨rho.matrix, rho.positive.isHermitian⟩
  nonneg := HermitianMat.zero_le_iff.mpr rho.positive
  tr := by
    rw [HermitianMat.trace_eq_re_trace]
    change rho.matrix.trace.re = 1
    rw [rho.trace_one]
    rfl

@[simp] theorem toMState_matrix {n : ℕ} (rho : State n) :
    (toMState rho).m = rho.matrix := rfl

/-- The reverse map uses the same matrix, including the complex trace-one
identity rather than merely its real part. -/
def fromMState {n : ℕ} (rho : MState (Fin n)) : State n where
  matrix := rho.m
  positive := rho.psd
  trace_one := by
    have h := rho.M.trace_eq_trace_rc
    rw [rho.tr] at h
    exact h.symm

@[simp] theorem from_to {n : ℕ} (rho : State n) : fromMState (toMState rho) = rho := by
  cases rho
  rfl

@[simp] theorem to_from {n : ℕ} (rho : MState (Fin n)) : toMState (fromMState rho) = rho := by
  apply MState.m_inj
  rfl

/-- The two models give the identical real Born expectation of any actual
Hermitian test matrix. -/
theorem exp_val_eq_trace {n : ℕ} (rho : State n) (T : HermitianMat (Fin n) ℂ) :
    (toMState rho).exp_val T = (rho.matrix * T.mat).trace.re := by
  exact HermitianMat.inner_eq_re_trace _ _

/-- Kernel inclusion is invariant under the identical coordinate model. -/
theorem support_toMState {n : ℕ} {rho sigma : State n}
    (h : RelativeEntropy.supportIncluded rho sigma) :
    (toMState sigma).M.ker ≤ (toMState rho).M.ker := by
  intro x hx
  rw [HermitianMat.mem_ker_iff_mulVec_zero] at hx ⊢
  exact h hx

/-- Both finite spectral calculi use the same logarithm, with a change of base. -/
theorem spectralLog2_eq_scaled_log {n : ℕ} (rho : State n) :
    RelativeEntropy.spectralLog2 rho =
      (Real.log 2)⁻¹ • (toMState rho).M.log.mat := by
  rw [RelativeEntropy.spectralLog2_eq_cfc]
  have hf : Real.logb 2 = fun x : ℝ => (Real.log 2)⁻¹ * Real.log x := by
    funext x
    simp [Real.logb, div_eq_mul_inv, mul_comm]
  rw [hf]
  change ((toMState rho).M.cfc (fun x : ℝ => (Real.log 2)⁻¹ * Real.log x)).mat = _
  rw [HermitianMat.cfc_const_mul, HermitianMat.mat_smul]
  rfl

/-- The supported natural-log entropy is exactly the local finite trace formula in bits. -/
theorem entropy_toReal_base_two {n : ℕ} (rho sigma : State n)
    (hs : RelativeEntropy.supportIncluded rho sigma) :
    (qRelativeEnt (toMState rho) (toMState sigma)).toReal / Real.log 2 =
      RelativeEntropy.traceFormula rho sigma := by
  have hq := qRelativeEnt_ker (support_toMState hs)
  have hr := congrArg EReal.toReal hq
  simp only [EReal.toReal_coe_ennreal, EReal.toReal_coe] at hr
  rw [hr, HermitianMat.inner_eq_re_trace]
  rw [RelativeEntropy.traceFormula, spectralLog2_eq_scaled_log,
    spectralLog2_eq_scaled_log, ← smul_sub, Matrix.mul_smul, Matrix.trace_smul]
  simp only [HermitianMat.mat_sub, toMState_matrix, Complex.smul_re, smul_eq_mul]
  change (rho.matrix * ((toMState rho).M.log.mat -
    (toMState sigma).M.log.mat)).trace.re / Real.log 2 = _
  rw [div_eq_mul_inv, mul_comm]

end QuantumChannelStein.PhyslibStateBridge
