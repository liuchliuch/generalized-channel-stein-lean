import GeneralizedChannelStein.CompletionPadding
import GeneralizedChannelStein.IsometricCompletionStatement

/-! Exact conversion between logarithmic loss and the final CP coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CompletionLossOrder
open QuantumChannelStein
variable {a b : ℕ}

theorem exp_log_loss (H r : ℝ) (hH : 0<H) (hr : 0<r) (m : ℕ) :
    (2:ℝ)^(1+2*Real.logb 2 H+(m:ℝ)*Real.logb 2 r)=2*H^2*r^m := by
  rw [Real.rpow_add (by norm_num),Real.rpow_add (by norm_num),Real.rpow_one]
  have h1 : (2:ℝ)^(2*Real.logb 2 H)=H^2 := by
    rw [mul_comm (2:ℝ),Real.rpow_mul (by norm_num),Real.rpow_logb (by norm_num) (by norm_num) hH]
    exact Real.rpow_two H
  have h2 : (2:ℝ)^((m:ℝ)*Real.logb 2 r)=r^m := by
    rw [mul_comm (m:ℝ),Real.rpow_mul (by norm_num),Real.rpow_logb (by norm_num) (by norm_num) hr,Real.rpow_natCast]
  rw [h1,h2]

theorem exp_log_power (r : ℝ) (hr : 0<r) (n : ℕ) :
    (2:ℝ)^((n:ℝ)*Real.logb 2 r)=r^n := by
  rw [mul_comm (n:ℝ),Real.rpow_mul (by norm_num),Real.rpow_logb (by norm_num) (by norm_num) hr,Real.rpow_natCast]

/-- Scaling the proved channel domination to the precise requested exponent. -/
theorem domination_at_loss (L S : KrausChannel a b) (p C E R : ℝ) (hp : 0<p)
    (hdom : MatrixMap.CPLe L.toLinearMap (Complex.ofReal C•S.toLinearMap))
    (hC : p*C≤(2:ℝ)^E) (hER : E≤R) :
    MatrixMap.CPLe (Complex.ofReal (p*(2:ℝ)^(-R))•L.toLinearMap) S.toLinearMap := by
  have hpow : 0<(2:ℝ)^R := Real.rpow_pos_of_pos (by norm_num) _
  have hb : p*C≤(2:ℝ)^R := hC.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hER)
  have hs : 0≤p*(2:ℝ)^(-R) := by positivity
  have hscaled := CloseBranchCompletion.cpLe_smul hdom hs
  simp only [smul_smul,← Complex.ofReal_mul] at hscaled
  have hmul : (p*(2:ℝ)^(-R))*C≤1 := by
    rw [Real.rpow_neg (by norm_num)]
    have hh := mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hpow.le)
    rw [mul_inv_cancel₀ hpow.ne'] at hh
    nlinarith
  have h := FreeAmplification.cpLe_scalar_mono _ S hmul hscaled
  simpa only [Complex.ofReal_one,one_smul] using h

end GeneralizedChannelStein.CompletionLossOrder
