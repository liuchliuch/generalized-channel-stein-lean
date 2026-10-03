import GeneralizedChannelStein.CompletionStatement
import GeneralizedChannelStein.NearSubadditive

/-! # Uniform finite and asymptotic scalar bounds for the literal completion loss -/
noncomputable section
namespace GeneralizedChannelStein.CompletionLossScalars
open Filter
open scoped Topology

/-- The paper's n^(2/3) log₂(n+1) scale. -/
def lossScale (n : ℕ) : ℝ := (n:ℝ)^((2:ℝ)/3)*Real.logb 2 ((n:ℝ)+1)

theorem one_le_lossScale (n : ℕ) (hn : 0<n) : 1 ≤ lossScale n := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hp : 1≤(n:ℝ)^((2:ℝ)/3) := Real.one_le_rpow hn1 (by norm_num)
  have hl : 1≤Real.logb 2 ((n:ℝ)+1) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤(n:ℝ)+1 by linarith)
    simpa only [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using h
  exact one_le_mul_of_one_le_of_one_le hp hl

/-- A fixed radius costs a fixed multiple of the paper's scalar loss. -/
theorem completionLoss_le (K : ℝ) (hK : 0≤K) (n : ℕ) (hn : 0<n)
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
    completionLoss K n δ ≤ K*(1-Real.logb 2 δ)*lossScale n := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hl : 1≤Real.logb 2 ((n:ℝ)+1) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤(n:ℝ)+1 by linarith)
    simpa only [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using h
  have hdlog : Real.logb 2 δ ≤ 0 := Real.logb_nonpos (by norm_num) hδ.le hδ1
  have hlog : Real.logb 2 ((n:ℝ)+1)-Real.logb 2 δ ≤
      (1-Real.logb 2 δ)*Real.logb 2 ((n:ℝ)+1) := by
    nlinarith [mul_nonneg (neg_nonneg.mpr hdlog) (sub_nonneg.mpr hl)]
  unfold completionLoss lossScale
  rw [Real.logb_div (by positivity : (n:ℝ)+1≠0) hδ.ne']
  have h := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg n) ((2:ℝ)/3)))
  convert h using 1
  ring

/-- A bounded scalar offset is absorbed uniformly for every positive integer. -/
theorem completionLoss_sub_log_le (K : ℝ) (hK : 0≤K) (n : ℕ) (hn : 0<n)
    (δ m : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hm : 0<m) (hm1 : m≤1) :
    completionLoss K n δ - Real.logb 2 m ≤
      (K*(1-Real.logb 2 δ)-Real.logb 2 m)*lossScale n := by
  have hg := completionLoss_le K hK n hn δ hδ hδ1
  have hmLog : Real.logb 2 m ≤ 0 := Real.logb_nonpos (by norm_num) hm.le hm1
  have hs := one_le_lossScale n hn
  have hconst := mul_le_mul_of_nonneg_left hs (neg_nonneg.mpr hmLog)
  nlinarith

/-- The exact paper loss is sublinear along all integer blocklengths. -/
theorem normalized_loss_tendsto_zero :
    Tendsto (fun n : ℕ => lossScale n/(n:ℝ)) atTop (𝓝 0) := by
  let C : ℝ := 6*(2:ℝ)^((1:ℝ)/6)/Real.log 2
  have hpow : Tendsto (fun n : ℕ => (n:ℝ)^(-((1:ℝ)/6))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun n : ℕ => C*(n:ℝ)^(-((1:ℝ)/6))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact div_nonneg (le_trans (by norm_num) (one_le_lossScale n hn)) (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    have h := NearSubadditive.logarithmic_error_le_power n hn
    change lossScale n ≤ C*(n:ℝ)^((5:ℝ)/6) at h
    have hh := div_le_div_of_nonneg_right h hnR.le
    have heq : (n:ℝ)^((5:ℝ)/6)/(n:ℝ) = (n:ℝ)^(-((1:ℝ)/6)) := by
      calc
        _ = (n:ℝ)^((5:ℝ)/6)/(n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub hnR]; norm_num
    simpa only [mul_div_assoc,heq] using hh

end GeneralizedChannelStein.CompletionLossScalars
