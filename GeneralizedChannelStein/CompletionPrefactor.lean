import GeneralizedChannelStein.CompletionStatement
import GeneralizedChannelStein.CompletionScalars

noncomputable section
namespace GeneralizedChannelStein.CompletionPrefactor

def adjustedConstant (K t : ℝ) : ℝ := K+max 0 (-Real.logb 2 t)

theorem adjustedConstant_nonneg {K : ℝ} (hK : 0 ≤ K) (t : ℝ) :
    0 ≤ adjustedConstant K t := add_nonneg hK (le_max_left _ _)

theorem completionScale_ge_one {n : ℕ} {δ : ℝ} (hn : 0 < n)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/16) :
    1 ≤ (n:ℝ)^((2:ℝ)/3)*Real.logb 2 (((n:ℝ)+1)/δ) := by
  have hs := CompletionScalars.blockScale_ge_one hn
  have hlog : 1 ≤ Real.logb 2 (((n:ℝ)+1)/δ) := by
    have hratio : (2:ℝ) ≤ ((n:ℝ)+1)/δ := by
      apply (le_div_iff₀ hδ).mpr
      have hn0 : (0:ℝ) ≤ n := by positivity
      linarith
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<2) hratio
    simpa using hh
  change 1 ≤ (n:ℝ)^((2:ℝ)/3) at hs
  nlinarith

/-- The fixed extension factor is absorbed into a constant chosen before n and δ. -/
theorem absorb_prefactor {t p β K δ : ℝ} {n : ℕ}
    (ht : 0 < t) (hp : t*β ≤ p) (hβ : 0 ≤ β)
    (hn : 0 < n) (hδ : 0 < δ) (hδ1 : δ ≤ 1/16) :
    β*(2:ℝ)^(-completionLoss (adjustedConstant K t) n δ) ≤
      p*(2:ℝ)^(-completionLoss K n δ) := by
  have hs := completionScale_ge_one hn hδ hδ1
  have hextra := mul_le_mul_of_nonneg_left hs (le_max_left 0 (-Real.logb 2 t))
  have hexp : -completionLoss (adjustedConstant K t) n δ ≤
      Real.logb 2 t + (-completionLoss K n δ) := by
    unfold completionLoss adjustedConstant
    nlinarith [le_max_right 0 (-Real.logb 2 t)]
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hexp
  rw [Real.rpow_add (by norm_num : (0:ℝ)<2),
    Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ) ≠ 1) ht] at hpow
  calc
    _ ≤ β*(t*(2:ℝ)^(-completionLoss K n δ)) := mul_le_mul_of_nonneg_left hpow hβ
    _ = (t*β)*(2:ℝ)^(-completionLoss K n δ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (by norm_num) _)

/-- Exactly the constant requested by the completion statement, without t≤1. -/
theorem completion_prefactor_bounds {t p β K δ : ℝ} {n : ℕ}
    (ht : 0 < t) (hp : t*β ≤ p) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hn : 0 < n) (hδ : 0 < δ) (hδ1 : δ ≤ 1/16) :
    0 ≤ K+max 0 (-Real.logb 2 t) ∧
    β*(2:ℝ)^(-completionLoss (K+max 0 (-Real.logb 2 t)) n δ) ≤
      p*(2:ℝ)^(-completionLoss K n δ) :=
  ⟨adjustedConstant_nonneg hK t,absorb_prefactor ht hp hβ hn hδ hδ1⟩

end GeneralizedChannelStein.CompletionPrefactor
