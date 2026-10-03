import GeneralizedChannelStein.CompletionLossScalars

noncomputable section
namespace GeneralizedChannelStein.AppendixCompletionScalars
open CompletionLossScalars

def envelopeConstant (K : ℝ) : ℝ := 10*K*(6*(2:ℝ)^((1:ℝ)/6)/Real.log 2)+2

theorem envelopeConstant_nonneg {K : ℝ} (hK : 0≤K) : 0≤envelopeConstant K := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold envelopeConstant
  positivity

theorem fixed_radius_loss_le {K : ℝ} (hK : 0≤K) {n : ℕ} (hn : 0<n) :
    completionLoss K n (1/16) ≤
      5*K*(6*(2:ℝ)^((1:ℝ)/6)/Real.log 2)*(n:ℝ)^((5:ℝ)/6) := by
  have h := completionLoss_le K hK n hn (1/16) (by norm_num) (by norm_num)
  have hlog : Real.logb 2 (1/16:ℝ) = -4 := by
    rw [one_div,Real.logb_inv,show (16:ℝ)=2^4 by norm_num,Real.logb_pow]
    norm_num
  rw [hlog] at h
  have hp := mul_le_mul_of_nonneg_left (NearSubadditive.logarithmic_error_le_power n hn)
    (show 0≤5*K by positivity)
  change 5*K*lossScale n ≤ _ at hp
  have hh : completionLoss K n (1/16) ≤ 5*K*lossScale n := by
    nlinarith only [h]
  exact hh.trans (by nlinarith only [hp])

theorem fixed_radius_sum_le {K : ℝ} (hK : 0≤K) {n m : ℕ} (hn : 0<n) (hm : 0<m) :
    completionLoss K n (1/16)+completionLoss K m (1/16)+2 ≤
      envelopeConstant K*((n+m:ℕ):ℝ)^((5:ℝ)/6) := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hnle : (n:ℝ)^((5:ℝ)/6) ≤ ((n+m:ℕ):ℝ)^((5:ℝ)/6) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_add_right n m) (by norm_num)
  have hmle : (m:ℝ)^((5:ℝ)/6) ≤ ((n+m:ℕ):ℝ)^((5:ℝ)/6) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_add_left m n) (by norm_num)
  have hs : 1 ≤ ((n+m:ℕ):ℝ)^((5:ℝ)/6) :=
    Real.one_le_rpow (by exact_mod_cast (show 1≤n+m by omega)) (by norm_num)
  have hcoef : 0≤5*K*(6*(2:ℝ)^((1:ℝ)/6)/Real.log 2) := by positivity
  have hnB := (fixed_radius_loss_le hK hn).trans (mul_le_mul_of_nonneg_left hnle hcoef)
  have hmB := (fixed_radius_loss_le hK hm).trans (mul_le_mul_of_nonneg_left hmle hcoef)
  unfold envelopeConstant
  nlinarith

theorem exists_fixed_radius_envelope (K : ℝ) (hK : 0≤K) :
    ∃ C : ℝ, 0≤C ∧ ∀ n m : ℕ, 0<n → 0<m →
      completionLoss K n (1/16)+completionLoss K m (1/16)+2 ≤
        C*((n+m:ℕ):ℝ)^((5:ℝ)/6) :=
  ⟨envelopeConstant K,envelopeConstant_nonneg hK,fun _ _ hn hm => fixed_radius_sum_le hK hn hm⟩

end GeneralizedChannelStein.AppendixCompletionScalars
