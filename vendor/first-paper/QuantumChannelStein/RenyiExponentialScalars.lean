import QuantumChannelStein.SandwichedRenyiBasics

/-! # Uniform scalar estimates for the exponential Rényi bound -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open RelativeEntropy
variable {n : ℕ}

/-- Taking a logarithm of the quasi-divergence root uses its proved strict positivity. -/
theorem renyi_le_of_quasi_root_le (α : ℝ) (hα : 1 < α) (ρ σ : State n)
    (hs : supportIncluded ρ σ) (R : ℝ)
    (hR : quasi α ρ.matrix σ.matrix ^ (1 / (2 * α)) ≤ R) :
    renyi α hα ρ σ ≤ ((2 * α / (α - 1)) * Real.logb 2 R : ℝ) := by
  have ha : 0 < α := by linarith
  have hm : 0 < α - 1 := sub_pos.mpr hα
  have hq := state_quasi_pos α hα ρ σ hs
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (Real.rpow_pos_of_pos hq (1 / (2 * α))) hR
  rw [Real.logb_rpow_eq_mul_logb_of_pos hq] at hl
  rw [renyi_of_supportIncluded α hα ρ σ hs]
  apply EReal.coe_le_coe_iff.mpr
  calc
    Real.logb 2 (quasi α ρ.matrix σ.matrix) / (α - 1) =
        (2 * α / (α - 1)) * ((1 / (2 * α)) * Real.logb 2 (quasi α ρ.matrix σ.matrix)) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

/-- An exponential root bound gives a linear block-entropy bound with an explicit constant. -/
theorem renyi_le_of_quasi_root_exponential (α : ℝ) (hα : 1 < α) (ρ σ : State n)
    (hs : supportIncluded ρ σ) (C M k : ℝ) (hC : 0 < C)
    (hR : quasi α ρ.matrix σ.matrix ^ (1 / (2 * α)) ≤
      C * (2 : ℝ) ^ (k * ((α - 1) / (2 * α)) * M)) :
    renyi α hα ρ σ ≤ (k * M + (2 * α / (α - 1)) * Real.logb 2 C : ℝ) := by
  have h := renyi_le_of_quasi_root_le α hα ρ σ hs _ hR
  rw [Real.logb_mul hC.ne' (Real.rpow_pos_of_pos (by norm_num) _).ne',
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0 : ℝ) < 2), Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
  have he : 2 * α / (α - 1) * (Real.logb 2 C + k * ((α - 1) / (2 * α)) * M * 1) =
      k * M + (2 * α / (α - 1)) * Real.logb 2 C := by
    field_simp [(by linarith : α ≠ 0), (sub_pos.mpr hα).ne']
    ring
  rwa [he] at h

end QuantumChannelStein.SandwichedRenyi

namespace QuantumChannelStein.RenyiExponentialScalars

def envelopeConstant (α K : ℝ) : ℝ :=
  (1 + K) ^ (1 / α) + K ^ (1 / α) * (4 : ℝ) ^ ((α - 1) / (2 * α))

theorem envelopeConstant_pos (α K : ℝ) (hK : 0 < K) : 0 < envelopeConstant α K := by
  unfold envelopeConstant
  positivity

/-- The error exponent is converted exactly to base two, with the natural logarithm factor. -/
theorem residual_exponential_identity (α : ℝ) (hα : 1 < α) (K γ k L : ℝ) (hK : 0 < K) :
    (K * Real.exp (-γ * k)) ^ (1 / α) *
      (4 * (2 : ℝ) ^ (k * L)) ^ ((α - 1) / (2 * α)) =
    (K ^ (1 / α) * (4 : ℝ) ^ ((α - 1) / (2 * α))) *
      (2 : ℝ) ^ (k * ((α - 1) / (2 * α)) *
        (L - 2 * γ / ((α - 1) * Real.log 2))) := by
  have ha : α ≠ 0 := by linarith
  have hm : α - 1 ≠ 0 := (sub_pos.mpr hα).ne'
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [Real.mul_rpow hK.le (Real.exp_pos _).le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg (by norm_num) _),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.exp_mul]
  have he : Real.exp (-γ * k * (1 / α)) * (2 : ℝ) ^ (k * L * ((α - 1) / (2 * α))) =
      (2 : ℝ) ^ (k * ((α - 1) / (2 * α)) *
        (L - 2 * γ / ((α - 1) * Real.log 2))) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
    congr 1
    field_simp
    ring
  calc
    _ = (K ^ (1 / α) * (4 : ℝ) ^ ((α - 1) / (2 * α))) *
        (Real.exp (-γ * k * (1 / α)) * (2 : ℝ) ^ (k * L * ((α - 1) / (2 * α)))) := by ring
    _ = _ := by rw [he]

/-- Uniformly bound the two actual Lemma 3.8 summands by one exponential. -/
theorem two_term_envelope (α : ℝ) (hα : 1 < α) (K γ k S L : ℝ)
    (hK : 0 < K) (hγ : 0 ≤ γ) (hk : 0 ≤ k) :
    (1 + K * Real.exp (-γ * k)) ^ (1 / α) *
        (2 : ℝ) ^ (k * ((α - 1) / (2 * α)) * S) +
      (K * Real.exp (-γ * k)) ^ (1 / α) *
        (4 * (2 : ℝ) ^ (k * L)) ^ ((α - 1) / (2 * α)) ≤
    envelopeConstant α K * (2 : ℝ) ^ (k * ((α - 1) / (2 * α)) *
      max S (L - 2 * γ / ((α - 1) * Real.log 2))) := by
  have ha : 0 < α := by linarith
  have hm : 0 < α - 1 := sub_pos.mpr hα
  have hq : 0 ≤ k * ((α - 1) / (2 * α)) := by positivity
  have he : Real.exp (-γ * k) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hA : (1 + K * Real.exp (-γ * k)) ^ (1 / α) ≤ (1 + K) ^ (1 / α) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    nlinarith
  have hpow0 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_left (le_max_left S (L - 2 * γ / ((α - 1) * Real.log 2))) hq)
  have hpow1 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (mul_le_mul_of_nonneg_left (le_max_right S (L - 2 * γ / ((α - 1) * Real.log 2))) hq)
  rw [residual_exponential_identity α hα K γ k L hK]
  calc
    _ ≤ (1 + K) ^ (1 / α) * _ +
        (K ^ (1 / α) * (4 : ℝ) ^ ((α - 1) / (2 * α))) * _ := by
      exact add_le_add
        (mul_le_mul hA hpow0 (Real.rpow_nonneg (by norm_num) _) (by positivity))
        (mul_le_mul_of_nonneg_left hpow1 (by positivity))
    _ = _ := by unfold envelopeConstant; ring

end QuantumChannelStein.RenyiExponentialScalars
