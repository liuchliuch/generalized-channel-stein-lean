import QuantumChannelStein.SandwichedSumBound
import QuantumChannelStein.RenyiExponentialScalars

/-! # The uniform Rényi estimate for an actual purification decomposition -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix RenyiExponentialScalars
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n e : ℕ}

theorem quasi_root_le_exponential_of_decomposition (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (ρ σ : State n) (F₀ F₁ : Matrix (Fin n) (Fin e) ℂ)
    (hρ : (F₀ + F₁) * (F₀ + F₁)ᴴ = ρ.matrix)
    (K γ k S L : ℝ) (hK : 0 < K) (hγ : 0 ≤ γ) (hk : 0 ≤ k)
    (h₀ : ((2 : ℝ) ^ (k * S) • σ.matrix - F₀ * F₀ᴴ).PosSemidef)
    (h₁ : ((4 * (2 : ℝ) ^ (k * L)) • σ.matrix - F₁ * F₁ᴴ).PosSemidef)
    (hF₀ : frobeniusNorm F₀ ≤ 1 + K * Real.exp (-γ * k))
    (hF₁ : frobeniusNorm F₁ ≤ K * Real.exp (-γ * k)) :
    quasi α ρ.matrix σ.matrix ^ (1 / (2 * α)) ≤
      envelopeConstant α K * (2 : ℝ) ^ (k * ((α - 1) / (2 * α)) *
        max S (L - 2 * γ / ((α - 1) * Real.log 2))) := by
  have ha : 0 < α := by linarith
  have h := lemma_3_8_sum α hα hα2 σ F₀ F₁ ((2 : ℝ) ^ (k * S))
    (4 * (2 : ℝ) ^ (k * L)) (by positivity) (by positivity) h₀ h₁
  rw [hρ, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hexp : k * S * ((α - 1) / (2 * α)) = k * ((α - 1) / (2 * α)) * S := by ring
  rw [hexp] at h
  have hn₀ := Real.rpow_le_rpow (frobeniusNorm_nonneg F₀) hF₀ (by positivity : 0 ≤ 1 / α)
  have hn₁ := Real.rpow_le_rpow (frobeniusNorm_nonneg F₁) hF₁ (by positivity : 0 ≤ 1 / α)
  apply h.trans
  calc
    _ ≤ (1 + K * Real.exp (-γ * k)) ^ (1 / α) *
          (2 : ℝ) ^ (k * ((α - 1) / (2 * α)) * S) +
        (K * Real.exp (-γ * k)) ^ (1 / α) *
          (4 * (2 : ℝ) ^ (k * L)) ^ ((α - 1) / (2 * α)) := by
      simpa only [mul_comm] using add_le_add
        (mul_le_mul_of_nonneg_left hn₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
        (mul_le_mul_of_nonneg_left hn₁ (Real.rpow_nonneg (by positivity) _))
    _ ≤ _ := two_term_envelope α hα K γ k S L hK hγ hk

/-- The exact finite-block form of the quantitative bound, including its uniform constant. -/
theorem renyi_le_exponential_of_decomposition (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (ρ σ : State n) (F₀ F₁ : Matrix (Fin n) (Fin e) ℂ)
    (hρ : (F₀ + F₁) * (F₀ + F₁)ᴴ = ρ.matrix)
    (K γ k S L : ℝ) (hK : 0 < K) (hγ : 0 ≤ γ) (hk : 0 ≤ k)
    (h₀ : ((2 : ℝ) ^ (k * S) • σ.matrix - F₀ * F₀ᴴ).PosSemidef)
    (h₁ : ((4 * (2 : ℝ) ^ (k * L)) • σ.matrix - F₁ * F₁ᴴ).PosSemidef)
    (hF₀ : frobeniusNorm F₀ ≤ 1 + K * Real.exp (-γ * k))
    (hF₁ : frobeniusNorm F₁ ≤ K * Real.exp (-γ * k)) :
    renyi α hα ρ σ ≤
      (k * max S (L - 2 * γ / ((α - 1) * Real.log 2)) +
        (2 * α / (α - 1)) * Real.logb 2 (envelopeConstant α K) : ℝ) := by
  have hsum := sum_gram_domination σ.matrix F₀ F₁ ((2 : ℝ) ^ (k * S))
    (4 * (2 : ℝ) ^ (k * L)) h₀ h₁
  rw [hρ] at hsum
  have hs := SupportDomination.ker_le_of_posSemidef_smul_sub ρ.positive hsum
  exact renyi_le_of_quasi_root_exponential α hα ρ σ hs _ _ k (envelopeConstant_pos α K hK)
    (quasi_root_le_exponential_of_decomposition α hα hα2 ρ σ F₀ F₁ hρ K γ k S L hK hγ hk
      h₀ h₁ hF₀ hF₁)

end QuantumChannelStein.SandwichedRenyi
