import QuantumChannelStein.SandwichedRenyiBridge
import QuantumChannelStein.SandwichedQuasiExtended
import Quantum.QuantumEntropy.YoungInequality

/-! # Positive-matrix trace Hölder, including zero traces

This file transports the audited positive trace Young theorem and rescales
actual PSD matrices. It does not posit a Schatten norm triangle inequality.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix MatrixOperatorBridge
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
attribute [local instance] matrixCStar operatorCStar operatorStar operatorStarRing
variable {n : ℕ}

def powerTrace (p : ℝ) (X : Operator n) : ℝ := (CFC.rpow X p).trace.re

theorem powerTrace_nonneg (p : ℝ) (X : Operator n) : 0 ≤ powerTrace p X :=
  (Complex.nonneg_iff.mp CFC.rpow_nonneg.posSemidef.trace_nonneg).1

theorem matrix_trace_young {p q : ℝ} (hpq : p.HolderConjugate q)
    (X Y : Operator n) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (X * Y).trace.re ≤ powerTrace p X / p + powerTrace q Y / q := by
  have h := trace_young_inequality hpq (opEquiv n X) (opEquiv n Y)
    ((LinearMap.nonneg_iff_isPositive _).mp ((op_nonneg_iff X).mpr hX))
    ((LinearMap.nonneg_iff_isPositive _).mp ((op_nonneg_iff Y).mpr hY))
  change QuantumState.Tr (opEquiv n X * opEquiv n Y) ≤
    QuantumState.Tr (CFC.rpow (opEquiv n X) p) / (p : ℂ) +
      QuantumState.Tr (CFC.rpow (opEquiv n Y) q) / (q : ℂ) at h
  rw [← map_mul, ← op_rpow X hX, ← op_rpow Y hY] at h
  have hr := (Complex.le_def.mp h).1
  simpa only [QuantumState.Tr, trace_op, Complex.add_re, Complex.div_ofReal_re] using hr

/-- Inverting a positive exponent is valid even for a singular PSD matrix. -/
theorem rpow_inverse_exponent (X : Operator n) (hX : X.PosSemidef)
    (p : ℝ) (hp : 0 < p) : CFC.rpow (CFC.rpow X p) (1 / p) = X := by
  have h := CFC.rpow_rpow_of_exponent_nonneg X p (1 / p) hp.le
    (one_div_nonneg.mpr hp.le) hX.nonneg
  simpa only [CFC.rpow_eq_pow, show p * (1 / p) = 1 by field_simp,
    CFC.rpow_one X hX.nonneg] using h

theorem powerTrace_eq_zero_iff (X : Operator n) (hX : X.PosSemidef)
    (p : ℝ) (hp : 0 < p) : powerTrace p X = 0 ↔ X = 0 := by
  constructor
  · intro ht
    have hXP : (CFC.rpow X p).PosSemidef := CFC.rpow_nonneg.posSemidef
    have htrace : (CFC.rpow X p).trace = 0 := by
      apply Complex.ext
      · exact ht
      · exact (Complex.nonneg_iff.mp hXP.trace_nonneg).2.symm
    have hz := hXP.trace_eq_zero_iff.mp htrace
    have h := rpow_inverse_exponent X hX p hp
    rw [hz, CFC.zero_rpow (one_div_ne_zero hp.ne')] at h
    exact h.symm
  · rintro rfl
    simp only [powerTrace, CFC.zero_rpow hp.ne', Matrix.trace_zero, Complex.zero_re]

theorem powerTrace_pos (X : Operator n) (hX : X.PosSemidef) (hX0 : X ≠ 0)
    (p : ℝ) (hp : 0 < p) : 0 < powerTrace p X :=
  lt_of_le_of_ne (powerTrace_nonneg p X)
    (Ne.symm (mt (powerTrace_eq_zero_iff X hX p hp).mp hX0))

theorem powerTrace_smul (X : Operator n) (hX : X.PosSemidef)
    (t p : ℝ) (ht : 0 ≤ t) : powerTrace p (t • X) = t ^ p * powerTrace p X := by
  rw [powerTrace, rpow_real_smul X hX t p ht, Matrix.trace_smul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- Positive-matrix trace Hölder for arbitrary conjugate exponents,
including singular matrices and zero power traces. -/
theorem matrix_trace_holder {p q : ℝ} (hpq : p.HolderConjugate q)
    (X Y : Operator n) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (X * Y).trace.re ≤
      powerTrace p X ^ (1 / p) * powerTrace q Y ^ (1 / q) := by
  by_cases hX0 : X = 0
  · subst X
    simpa only [Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re] using
      mul_nonneg (Real.rpow_nonneg (powerTrace_nonneg p (0 : Operator n)) (1 / p))
        (Real.rpow_nonneg (powerTrace_nonneg q Y) (1 / q))
  by_cases hY0 : Y = 0
  · subst Y
    simpa only [Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re] using
      mul_nonneg (Real.rpow_nonneg (powerTrace_nonneg p X) (1 / p))
        (Real.rpow_nonneg (powerTrace_nonneg q (0 : Operator n)) (1 / q))
  have hTX := powerTrace_pos X hX hX0 p hpq.pos
  have hTY := powerTrace_pos Y hY hY0 q hpq.symm.pos
  let u : ℝ := powerTrace p X ^ (1 / p)
  let v : ℝ := powerTrace q Y ^ (1 / q)
  have hu : 0 < u := Real.rpow_pos_of_pos hTX _
  have hv : 0 < v := Real.rpow_pos_of_pos hTY _
  have hup : u ^ p = powerTrace p X := by
    dsimp [u]
    rw [← Real.rpow_mul hTX.le, one_div_mul_cancel hpq.ne_zero, Real.rpow_one]
  have hvq : v ^ q = powerTrace q Y := by
    dsimp [v]
    rw [← Real.rpow_mul hTY.le, one_div_mul_cancel hpq.symm.ne_zero, Real.rpow_one]
  have hnX : powerTrace p (u⁻¹ • X) = 1 := by
    rw [powerTrace_smul X hX _ _ (inv_nonneg.mpr hu.le), Real.inv_rpow hu.le p,
      hup, inv_mul_cancel₀ hTX.ne']
  have hnY : powerTrace q (v⁻¹ • Y) = 1 := by
    rw [powerTrace_smul Y hY _ _ (inv_nonneg.mpr hv.le), Real.inv_rpow hv.le q,
      hvq, inv_mul_cancel₀ hTY.ne']
  have h := matrix_trace_young hpq (u⁻¹ • X) (v⁻¹ • Y)
    (hX.smul (inv_nonneg.mpr hu.le)) (hY.smul (inv_nonneg.mpr hv.le))
  rw [hnX, hnY, one_div, one_div, hpq.inv_add_inv_eq_one] at h
  have heq : ((u⁻¹ • X) * (v⁻¹ • Y)).trace.re = (X * Y).trace.re / (u * v) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul]
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  rw [heq] at h
  exact (div_le_one (mul_pos hu hv)).mp h

end QuantumChannelStein.SandwichedRenyi
