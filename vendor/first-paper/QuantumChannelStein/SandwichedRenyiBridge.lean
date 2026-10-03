import QuantumChannelStein.SandwichedRenyi
import QuantumChannelStein.RelativeEntropyDPIBridge
import Quantum.QuantumEntropy.SandwichedRenyiNonNeg

/-! # Exact transport of the above-one matrix Rényi family to the audited NN API -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix RelativeEntropy MatrixOperatorBridge
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

attribute [local instance] matrixCStar operatorCStar operatorStar operatorStarRing
variable {n m : ℕ}

theorem op_rpow (A : Operator n) (hA : A.PosSemidef) (p : ℝ) :
    opEquiv n (CFC.rpow A p) = CFC.rpow (opEquiv n A) p := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA.nonneg,
    CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real ((op_nonneg_iff A).mpr hA)]
  exact op_cfc A hA.isHermitian _

theorem op_sandwichedOperator (α : ℝ) (A B : Operator n) (hB : B.PosSemidef) :
    opEquiv n (sandwichedOperator α A B) =
      CFC.rpow (opEquiv n B) (sandwichExponent α) * opEquiv n A *
        CFC.rpow (opEquiv n B) (sandwichExponent α) := by
  rw [sandwichedOperator, map_mul, map_mul, op_rpow B hB]

theorem quasi_eq_external (α : ℝ) (A B : Operator n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    quasi α A B =
      (SandwichedRenyiRelativeEntropy.sandwichedQuasi α (opEquiv n A) (opEquiv n B)).re := by
  have h := op_rpow (sandwichedOperator α A B) (sandwichedOperator_positive α hA) α
  rw [op_sandwichedOperator α A B hB] at h
  have ht := congrArg (fun X => (QuantumState.Tr X).re) h
  change (LinearMap.trace ℂ (H n) (opEquiv n _)).re = _ at ht
  rw [trace_op] at ht
  exact ht

/-- Trace-one normalization removes the denominator in the external core,
and a strictly positive factor converts nats to bits. -/
theorem renyi_real_eq_external (α : ℝ) (ρ σ : State n) :
    Real.logb 2 (quasi α ρ.matrix σ.matrix) / (α - 1) =
      (Real.log 2)⁻¹ * SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv
        α (opEquiv n ρ.matrix) (opEquiv n σ.matrix) := by
  have ht : QuantumState.Tr (opEquiv n ρ.matrix) = 1 :=
    (trace_op ρ.matrix).trans ρ.trace_one
  rw [SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv, ht,
    ← quasi_eq_external α ρ.matrix σ.matrix ρ.positive σ.positive]
  simp only [Complex.one_re, div_one, Real.logb, div_eq_mul_inv]
  ring

/-- Exact support-aware EReal correspondence, including singular supports. -/
theorem renyi_eq_external [Nontrivial (H n)] (α : ℝ) (hα : 1 < α) (ρ σ : State n) :
    renyi α hα ρ σ = (↑((Real.log 2)⁻¹) : EReal) *
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN
        α (opEquiv n ρ.matrix) (opEquiv n σ.matrix) := by
  classical
  have hnot : ¬α < 1 := not_lt.mpr hα.le
  by_cases hs : supportIncluded ρ σ
  · have he := (supportIncluded_iff_external ρ σ).mp hs
    rw [renyi_of_supportIncluded _ _ _ _ hs,
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN]
    simp only [hnot, false_and, or_false, he, not_true_eq_false, and_false, if_false]
    rw [← EReal.coe_mul, renyi_real_eq_external]
  · have he := mt (supportIncluded_iff_external ρ σ).mpr hs
    rw [renyi_of_not_supportIncluded _ _ _ _ hs,
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN]
    simp only [hα, he, not_false_eq_true, true_and, true_or, if_true]
    rw [EReal.coe_mul_top_of_pos (inv_pos.mpr (Real.log_pos (by norm_num : (1:ℝ)<2)))]

/-- Genuine Rényi data processing for all above-one orders and arbitrary
finite density matrices, with no full-rank or support assumption. -/
theorem renyi_data_processing (α : ℝ) (hα : 1 < α)
    (Φ : KrausChannel n m) (ρ σ : State n) :
    renyi α hα (Φ.onState ρ) (Φ.onState σ) ≤ renyi α hα ρ σ := by
  letI : NeZero n := ⟨Nat.ne_of_gt (state_dimension_pos ρ)⟩
  letI : NeZero m := ⟨Nat.ne_of_gt (state_dimension_pos (Φ.onState ρ))⟩
  rw [renyi_eq_external, renyi_eq_external]
  have h := SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN_monotone
    (channelCPTP Φ) (by linarith : (1:ℝ)/2 ≤ α) (ne_of_gt hα)
    ((op_nonneg_iff ρ.matrix).mpr ρ.positive) ((op_nonneg_iff σ.matrix).mpr σ.positive)
  simp only [channelCPTP_op] at h
  exact mul_le_mul_of_nonneg_left h
    (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Real.log_nonneg (by norm_num))))

end QuantumChannelStein.SandwichedRenyi
