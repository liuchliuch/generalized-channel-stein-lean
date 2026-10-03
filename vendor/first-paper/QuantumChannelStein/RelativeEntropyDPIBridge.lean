import QuantumChannelStein.RelativeEntropy
import QuantumChannelStein.KrausOperatorBridge
import Quantum.QuantumEntropy.SandwichedRenyiUmegaki
import Mathlib.Data.EReal.Inv

/-! Exact base and normalization bridge to the audited external Umegaki DPI. -/
noncomputable section
namespace QuantumChannelStein.MatrixOperatorBridge
open Matrix RelativeEntropy
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n m : ℕ}

attribute [local instance] operatorCStar operatorStar operatorStarRing
set_option backward.isDefEq.respectTransparency false

theorem spectralLog2_eq_invlog_smul (ρ : State n) :
    spectralLog2 ρ = ((Real.log 2)⁻¹ : ℝ) • cfc Real.log ρ.matrix := by
  rw [spectralLog2_eq_cfc]
  have hf : Real.logb 2 = fun x => (Real.log 2)⁻¹ * Real.log x := by
    funext x
    simp [Real.logb, div_eq_mul_inv, mul_comm]
  rw [hf, cfc_const_mul _ _ _ (ρ.matrix.finite_real_spectrum.continuousOn _)]

theorem traceFormula_eq_invlog_trace (ρ σ : State n) :
    traceFormula ρ σ = (Real.log 2)⁻¹ *
      (ρ.matrix * (cfc Real.log ρ.matrix - cfc Real.log σ.matrix)).trace.re := by
  rw [traceFormula, spectralLog2_eq_invlog_smul, spectralLog2_eq_invlog_smul,
    ← smul_sub, Matrix.mul_smul, Matrix.trace_smul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem operator_log_trace (ρ σ : State n) :
    QuantumState.Tr (opEquiv n ρ.matrix *
      (CFC.log (opEquiv n ρ.matrix) - CFC.log (opEquiv n σ.matrix))) =
      (ρ.matrix * (cfc Real.log ρ.matrix - cfc Real.log σ.matrix)).trace := by
  rw [← op_log _ ρ.positive.isHermitian, ← op_log _ σ.positive.isHermitian,
    ← map_sub, ← map_mul]
  exact trace_op _

theorem traceFormula_eq_external_norm (ρ σ : State n) :
    traceFormula ρ σ = (Real.log 2)⁻¹ *
      SandwichedRenyiRelativeEntropy.umegakiNorm (opEquiv n ρ.matrix) (opEquiv n σ.matrix) := by
  rw [traceFormula_eq_invlog_trace, SandwichedRenyiRelativeEntropy.umegakiNorm,
    operator_log_trace]
  have htr : QuantumState.Tr (opEquiv n ρ.matrix) = 1 :=
    (trace_op ρ.matrix).trans ρ.trace_one
  rw [htr]
  simp

theorem supportIncluded_iff_external [Nontrivial (H n)] (ρ σ : State n) :
    supportIncluded ρ σ ↔
      SandwichedRenyiRelativeEntropy.suppLE (opEquiv n ρ.matrix) (opEquiv n σ.matrix) :=
  (ker_le_iff ρ.matrix σ.matrix).symm

theorem umegaki_eq_external [Nontrivial (H n)] (ρ σ : State n) :
    umegaki ρ σ = (↑((Real.log 2)⁻¹) : EReal) *
      SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN
        (opEquiv n ρ.matrix) (opEquiv n σ.matrix) := by
  classical
  by_cases h : supportIncluded ρ σ
  · have he := (supportIncluded_iff_external ρ σ).mp h
    rw [umegaki_of_supportIncluded _ _ h,
      SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN, if_pos he,
      ← EReal.coe_mul, traceFormula_eq_external_norm]
  · have he := mt (supportIncluded_iff_external ρ σ).mpr h
    rw [umegaki_of_not_supportIncluded _ _ h,
      SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN, if_neg he,
      EReal.coe_mul_top_of_pos (inv_pos.mpr (Real.log_pos (by norm_num : (1:ℝ)<2)))]

theorem umegaki_data_processing_of_nontrivial [Nontrivial (H n)] [Nontrivial (H m)]
    (Φ : KrausChannel n m) (ρ σ : State n) :
    umegaki (Φ.onState ρ) (Φ.onState σ) ≤ umegaki ρ σ := by
  rw [umegaki_eq_external, umegaki_eq_external]
  have h := SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN_monotone
    (channelCPTP Φ) ((op_nonneg_iff ρ.matrix).mpr ρ.positive)
    ((op_nonneg_iff σ.matrix).mpr σ.positive)
  simp only [channelCPTP_op] at h
  apply mul_le_mul_of_nonneg_left h
  exact EReal.coe_nonneg.mpr (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))

/-- A normalized finite state cannot inhabit dimension zero. -/
theorem state_dimension_pos (ρ : State n) : 0 < n := by
  apply Nat.pos_of_ne_zero
  intro h
  subst n
  have ht := ρ.trace_one
  simp [Matrix.trace] at ht

/-- Data processing for every concrete finite normalized Kraus channel and
all states, including singular inputs. No separate dimensional hypothesis is needed. -/
theorem umegaki_data_processing (Φ : KrausChannel n m) (ρ σ : State n) :
    umegaki (Φ.onState ρ) (Φ.onState σ) ≤ umegaki ρ σ := by
  letI : NeZero n := ⟨Nat.ne_of_gt (state_dimension_pos ρ)⟩
  letI : NeZero m := ⟨Nat.ne_of_gt (state_dimension_pos (Φ.onState ρ))⟩
  exact umegaki_data_processing_of_nontrivial Φ ρ σ

end QuantumChannelStein.MatrixOperatorBridge

namespace QuantumChannelStein.RelativeEntropy

/-- Umegaki data processing for concrete finite-dimensional quantum channels.
This theorem covers arbitrary density matrices, including singular support. -/
theorem umegaki_data_processing {n m : ℕ} (Φ : KrausChannel n m) (ρ σ : State n) :
    umegaki (Φ.onState ρ) (Φ.onState σ) ≤ umegaki ρ σ :=
  MatrixOperatorBridge.umegaki_data_processing Φ ρ σ

end QuantumChannelStein.RelativeEntropy
