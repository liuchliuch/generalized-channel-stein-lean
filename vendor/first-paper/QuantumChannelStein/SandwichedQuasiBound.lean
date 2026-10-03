import QuantumChannelStein.SandwichedPowerCalculus
import QuantumChannelStein.Testing
import QuantumChannelStein.SupportDomination

/-! # First inequality of Lemma 3.8

For positive semidefinite matrices `A ≤ t B`, `t ≥ 0` and `1 < α ≤ 2`,
the actual sandwiched quasi-divergence is at most `t^(α-1) Tr A`.
The proof uses the checked Löwner–Heinz theorem and explicitly cancels a
support projection at the singular boundary. No invertibility is assumed.
The trace factor is unnormalized; it is not an operator norm.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
attribute [local instance] matrixCStar
variable {n : ℕ}

/-- Positivity of the trace pairing converts operator order to trace order. -/
theorem trace_mul_mono (X Y Z : Operator n) (hX : X.PosSemidef) (hYZ : Y ≤ Z) :
    (X * Y).trace.re ≤ (X * Z).trace.re := by
  have h := (Complex.nonneg_iff.mp
    (trace_mul_nonnegative hX (sub_nonneg.mpr hYZ).posSemidef)).1
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h

/-- The negative sandwich preserves a domination inequality and turns the
alternative into its positive `1/α` power. -/
theorem sandwichedOperator_le (α : ℝ) (hα : 1 < α) (A B : Operator n)
    (hB : B.PosSemidef) (t : ℝ) (hdom : (t • B - A).PosSemidef) :
    sandwichedOperator α A B ≤ t • CFC.rpow B (1 / α) := by
  let P := CFC.rpow B (sandwichExponent α)
  have hP : P.PosSemidef := CFC.rpow_nonneg.posSemidef
  have h := hdom.mul_mul_conjTranspose_same P
  have hs : P * B * P = CFC.rpow B (1 / α) := sandwich_self_eq_rpow α hα B hB
  have h' : (t • CFC.rpow B (1 / α) - sandwichedOperator α A B).PosSemidef := by
    simpa only [hP.isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, hs] using h
  exact sub_nonneg.mp h'.nonneg

/-- The trace cancellation required in the singular case uses `A P = A`,
where `P` is the support projection of the alternative. -/
theorem trace_sandwiched_cancel (α : ℝ) (hα : 1 < α) (A B : Operator n)
    (hB : B.PosSemidef)
    (hsupport : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    (sandwichedOperator α A B * CFC.rpow B ((α - 1) / α)).trace = A.trace := by
  let P := CFC.rpow B (sandwichExponent α)
  let R := CFC.rpow B ((α - 1) / α)
  change (P * A * P * R).trace = A.trace
  rw [Matrix.mul_assoc (P * A) P R, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  change (A * (P * R * P)).trace = A.trace
  rw [show P * R * P = Pseudoinverse.supportProjection B hB from
    sandwich_powers_eq_supportProjection α hα B hB,
    Pseudoinverse.mul_supportProjection_of_ker_le A B hB hsupport]

/-- **Lemma 3.8, first assertion.** This covers arbitrary PSD alternatives,
not only trace-one alternatives, and includes zero matrices and `t=0`. -/
theorem quasi_le_of_domination (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (A B : Operator n) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) (hdom : (t • B - A).PosSemidef) :
    quasi α A B ≤ t ^ (α - 1) * A.trace.re := by
  let X := sandwichedOperator α A B
  have hX : X.PosSemidef := sandwichedOperator_positive α hA
  have ha0 : 0 < α := by linarith
  have hp0 : 0 < α - 1 := sub_pos.mpr hα
  have hpow : CFC.rpow X (α - 1) ≤
      CFC.rpow (t • CFC.rpow B (1 / α)) (α - 1) :=
    CFC.rpow_le_rpow (show α - 1 ∈ Set.Icc (0:ℝ) 1 from ⟨hp0.le, by linarith⟩)
      (sandwichedOperator_le α hα A B hB t hdom)
  have hBroot : (CFC.rpow B (1 / α)).PosSemidef := CFC.rpow_nonneg.posSemidef
  rw [rpow_real_smul (CFC.rpow B (1 / α)) hBroot t (α - 1) ht] at hpow
  have hpowers : CFC.rpow (CFC.rpow B (1 / α)) (α - 1) =
      CFC.rpow B ((α - 1) / α) := by
    have h := CFC.rpow_rpow_of_exponent_nonneg B (1 / α) (α - 1)
      (one_div_nonneg.mpr ha0.le) hp0.le hB.nonneg
    simpa only [CFC.rpow_eq_pow, show (1 / α) * (α - 1) = (α - 1) / α by ring] using h
  rw [hpowers] at hpow
  have hfactor : CFC.rpow X α = X * CFC.rpow X (α - 1) := by
    have h := rpow_add_of_sum_ne_zero X hX 1 (α - 1) (by linarith)
    rw [show (1 : ℝ) + (α - 1) = α by ring,
      show CFC.rpow X 1 = X from CFC.rpow_one X hX.nonneg] at h
    exact h
  have hsupport := SupportDomination.ker_le_of_posSemidef_smul_sub hA hdom
  change (CFC.rpow X α).trace.re ≤ _
  rw [hfactor]
  calc
    (X * CFC.rpow X (α - 1)).trace.re ≤
        (X * ((t ^ (α - 1) : ℝ) • CFC.rpow B ((α - 1) / α))).trace.re :=
      trace_mul_mono X _ _ hX hpow
    _ = t ^ (α - 1) * (X * CFC.rpow B ((α - 1) / α)).trace.re := by
      rw [Matrix.mul_smul, Matrix.trace_smul]
      simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    _ = t ^ (α - 1) * A.trace.re := by
      rw [trace_sandwiched_cancel α hα A B hB hsupport]

end QuantumChannelStein.SandwichedRenyi
