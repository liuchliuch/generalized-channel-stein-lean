import QuantumChannelStein.PositivePartTesting

/-! # Repairing a PSD Lagrange multiplier to a feasible channel-testing dual -/
noncomputable section
namespace QuantumChannelStein.TestingSDP
open Matrix PositivePartTesting
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator Kronecker

theorem norm_le_of_state_expectations {a : ℕ} (omega0 : State a)
    (W : Operator a) (hW : W.PosSemidef) (s : ℝ)
    (h : ∀ omega : State a, (W * omega.matrix).trace.re ≤ s) : ‖W‖ ≤ s := by
  letI : CStarAlgebra (Operator a) := CStarAlgebra.mk
  have hs : 0 ≤ s := (Complex.nonneg_iff.mp (trace_pairing_nonnegative hW omega0.positive)).1.trans (h omega0)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap W hs hW.nonneg).mpr
  rw [Algebra.algebraMap_eq_smul_one]
  apply sub_nonneg.mp
  apply Matrix.nonneg_iff_posSemidef.mpr
  apply (positive_iff_trace_pairing_nonnegative
    ((Matrix.PosSemidef.one.smul hs).isHermitian.sub hW.isHermitian)).mpr
  intro B hB
  let tr := B.trace.re
  have htr : 0 ≤ tr := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have hBtrace : B.trace = (tr : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp hB.trace_nonneg).2.symm
  by_cases hz : tr = 0
  · have hzero : B = 0 := hB.trace_eq_zero_iff.mp (by simpa [hz] using hBtrace)
    simp [hzero]
  · have htp : 0 < tr := lt_of_le_of_ne htr (Ne.symm hz)
    let omega : State a := ⟨tr⁻¹ • B, hB.smul (inv_nonneg.mpr htr), by
      rw [Matrix.trace_smul, hBtrace]
      simp only [Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hz, Complex.ofReal_one]⟩
    have hh := h omega
    change (W * (tr⁻¹ • B)).trace.re ≤ s at hh
    simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
    have hh' : (W * B).trace.re ≤ s * tr := by
      have hh' := mul_le_mul_of_nonneg_left hh htr
      rwa [← mul_assoc, mul_inv_cancel₀ hz, one_mul, mul_comm tr s] at hh'
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
      Matrix.trace_smul, Complex.sub_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact sub_nonneg.mpr hh'

theorem repair_lagrange_multiplier {a b : ℕ} (omega0 : State a)
    (Delta Y : BipartiteOperator a b) (hDelta : Delta.IsHermitian) (hY : Y.PosSemidef)
    (r : ℝ)
    (h : ∀ omega : State a, ∀ Q : BipartiteOperator a b,
      Q.PosSemidef → (1 - Q).PosSemidef →
      (Delta * Q).trace.re + (Y * (omega.matrix ⊗ₖ (1 : Operator b) - Q)).trace.re ≤ r) :
    ∃ D : DualFeasible Delta, D.value ≤ r := by
  let H := Delta - Y
  have hH : H.IsHermitian := hDelta.sub hY.isHermitian
  let P := positivePart H hH
  let Q := positiveProjection H hH
  have hP : P.PosSemidef := positivePart_positive H hH
  have hdom : (Y + P - Delta).PosSemidef := by
    convert positivePart_dominates H hH using 1
    dsimp [P, H]
    abel
  let D : DualFeasible Delta := ⟨Y + P, hY.add hP, hdom⟩
  refine ⟨D, ?_⟩
  have hbound : ∀ omega : State a,
      (KrausChannel.traceOutput Y * omega.matrix).trace.re ≤ r - P.trace.re := by
    intro omega
    have hh := h omega Q (positiveProjection_positive H hH)
      (positiveProjection_complement_positive H hH)
    have heq : (Delta * Q).trace.re +
        (Y * (omega.matrix ⊗ₖ (1 : Operator b) - Q)).trace.re =
        (KrausChannel.traceOutput Y * omega.matrix).trace.re + P.trace.re := by
      have hm : (Delta - Y) * Q = P := mul_positiveProjection H hH
      have ht := congrArg (fun Z => Z.trace.re) hm
      simp only [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at ht
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, traceOutput_pairing]
      linarith
    rw [heq] at hh
    linarith
  have hnormY := norm_le_of_state_expectations omega0 _ (traceOutput_positive hY)
    (r - P.trace.re) hbound
  have hnormP : ‖KrausChannel.traceOutput P‖ ≤ P.trace.re := by
    simpa only [trace_traceOutput] using positive_norm_le_trace (traceOutput_positive hP)
  change ‖KrausChannel.traceOutput (Y + P)‖ ≤ r
  have hadd : KrausChannel.traceOutput (Y + P) =
      KrausChannel.traceOutput Y + KrausChannel.traceOutput P := by
    ext i j
    simp [KrausChannel.traceOutput, Finset.sum_add_distrib]
  rw [hadd]
  exact (norm_add_le _ _).trans (by linarith)
end QuantumChannelStein.TestingSDP
