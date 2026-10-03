import GeneralizedChannelStein.LikelihoodThreshold
import Mathlib.Data.ENNReal.Real

/-! # Exact scalar conversion of the finite testing bound to a base-two exponent -/
noncomputable section
namespace GeneralizedChannelStein.LargeErrorScalars

/-- The factor two from the faithful mixture costs exactly one bit. -/
theorem exponent_lower (β : ENNReal) (hβ : 0<β) (hβtop : β<⊤) (t : ℝ)
    (h : β ≤ ENNReal.ofReal (2*(2:ℝ)^(-t))) :
    t-1 ≤ -Real.logb 2 β.toReal := by
  have hp : 0 < β.toReal := ENNReal.toReal_pos hβ.ne' hβtop.ne
  have hr : β.toReal ≤ 2*(2:ℝ)^(-t) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (by positivity)] at hh
  have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hp hr
  rw [Real.logb_mul (by norm_num : (2:ℝ)≠0)
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-t)).ne',
    show Real.logb 2 2 = 1 from by norm_num [Real.logb],
    Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)] at hh
  linarith

end GeneralizedChannelStein.LargeErrorScalars
