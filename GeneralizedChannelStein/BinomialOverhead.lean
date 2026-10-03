import GeneralizedChannelStein.InvariantOrbitDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The exact binomial spectral overhead is sublinear -/
noncomputable section
namespace GeneralizedChannelStein.BinomialOverhead
open Filter
open scoped Topology

def mass (d n : ℕ) : ℝ := ((n+d^2-1).choose (d^2-1) : ℕ)
def overhead (d n : ℕ) : ℝ := Real.logb 2 (mass d n)

theorem shifted_log_div_tendsto_zero (c : ℝ) (hc : 0<c) :
    Tendsto (fun n : ℕ => Real.logb 2 ((n:ℝ)+c)/(n:ℝ)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ => (n:ℝ)+c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+c)/((n:ℝ)+c)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hshift
  have hratio : Tendsto (fun n : ℕ => 1+c/(n:ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul c
    simpa only [mul_one_div,mul_zero,add_zero] using (tendsto_const_nhds (x:=(1:ℝ))).add h
  have h := (hlog.mul hratio).div_const (Real.log 2)
  simp only [zero_mul,zero_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := (Nat.cast_pos.mpr hn).ne'
  have hnc : (n:ℝ)+c≠0 := by positivity
  rw [Real.logb]
  field_simp

theorem normalized_overhead_tendsto_zero (d : ℕ) :
    Tendsto (fun n : ℕ => overhead d n/(n:ℝ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (d^2-1:ℕ)*
      (Real.logb 2 ((n:ℝ)+(d:ℝ)^2+1)/(n:ℝ))) atTop (𝓝 0) := by
    have h := (shifted_log_div_tendsto_zero ((d:ℝ)^2+1) (by positivity)).const_mul ((d^2-1:ℕ):ℝ)
    simpa only [mul_zero,add_assoc] using h
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hv : 1≤mass d n := by
      unfold mass
      exact_mod_cast InvariantOrbitDimension.binomial_mass_pos d n
    exact div_nonneg (Real.logb_nonneg (by norm_num) hv) (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hp : 0<mass d n := InvariantOrbitDimension.binomial_mass_real_pos d n
    have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hp
      (InvariantOrbitDimension.binomial_mass_real_le_polynomial d n)
    rw [Real.logb_pow] at h
    have hh := div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
    simpa only [overhead,mul_div_assoc] using hh

end GeneralizedChannelStein.BinomialOverhead
