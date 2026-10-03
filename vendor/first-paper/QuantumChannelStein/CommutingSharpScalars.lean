import QuantumChannelStein.GeometricMeanSelf

/-! # Scalar identities for the commuting geometric-mean program -/
noncomputable section
namespace QuantumChannelStein.CommutingSharpScalars

/-- Scalar counterpart of the supported mean, written with a quotient. -/
def scalarMean (p b x : ℝ) : ℝ := b * (x / b) ^ p

theorem scalarMean_candidate (α a b : ℝ) (hα : 1 < α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : b = 0 → a = 0) :
    scalarMean (1 / α) b (a ^ α * b ^ (1 - α)) = a := by
  by_cases hb0 : b = 0
  · simp [scalarMean, hb0, hs hb0]
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hdiv : (a ^ α * b ^ (1 - α)) / b = (a / b) ^ α := by
    have hbpow : b ^ (1 - α) = b ^ (-α) * b := by
      rw [show (1 - α : ℝ) = -α + 1 by ring, Real.rpow_add hbpos, Real.rpow_one]
    rw [hbpow, Real.div_rpow ha hb, Real.rpow_neg hb]
    field_simp

  rw [scalarMean, hdiv, ← Real.rpow_mul (div_nonneg ha hb), mul_one_div_cancel hα0.ne', Real.rpow_one]
  field_simp

theorem candidate_le_of_scalarMean_le (α a b x : ℝ) (hα : 1 < α)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hs : b = 0 → a = 0) (h : a ≤ scalarMean (1 / α) b x) :
    a ^ α * b ^ (1 - α) ≤ x := by
  by_cases hb0 : b = 0
  · simp [hb0, hs hb0, Real.zero_rpow (show α ≠ 0 by linarith), hx]
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hpow := Real.rpow_le_rpow ha h hα0.le
  unfold scalarMean at hpow
  rw [Real.mul_rpow hb (Real.rpow_nonneg (div_nonneg hx hb) _),
    ← Real.rpow_mul (div_nonneg hx hb), one_div_mul_cancel hα0.ne', Real.rpow_one] at hpow
  have hh := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hb (1 - α))
  have heq : (b ^ α * (x / b)) * b ^ (1 - α) = x := by
    calc
      _ = (b ^ α * b ^ (1 - α)) * (x / b) := by ring
      _ = b * (x / b) := by rw [← Real.rpow_add hbpos]; simp
      _ = x := by field_simp
  rw [heq] at hh
  exact hh

end QuantumChannelStein.CommutingSharpScalars
