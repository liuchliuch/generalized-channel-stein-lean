import QuantumChannelStein.RenyiExponentialScalars
import Mathlib.Topology.Instances.EReal.Lemmas

/-! # The elementary right-limit argument with the exact exponential-error correction -/
noncomputable section
namespace QuantumChannelStein.RenyiExponentialScalars
open Filter
open scoped Topology

/-- For fixed positive exponential decay, the second branch is eventually below any fixed slope. -/
theorem eventually_correction_le (S L γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ α : ℝ in 𝓝[>] (1 : ℝ), 1 < α ∧ α ≤ 2 ∧
      L - 2 * γ / ((α - 1) * Real.log 2) ≤ S := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have halpha : ∀ᶠ α : ℝ in 𝓝[>] (1 : ℝ), 1 < α ∧ α ≤ 2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))] with α ha hb
    exact ⟨ha, hb.le⟩
  by_cases hLS : L ≤ S
  · filter_upwards [halpha] with α hα
    refine ⟨hα.1, hα.2, ?_⟩
    have hm : 0 < α - 1 := sub_pos.mpr hα.1
    have hfrac : 0 ≤ 2 * γ / ((α - 1) * Real.log 2) := by positivity
    linarith
  · have hSL : 0 < L - S := sub_pos.mpr (lt_of_not_ge hLS)
    let δ : ℝ := 2 * γ / ((L - S) * Real.log 2)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    filter_upwards [halpha,
      nhdsWithin_le_nhds (eventually_lt_nhds (show (1 : ℝ) < 1 + δ by linarith))] with α hα hnear
    refine ⟨hα.1, hα.2, ?_⟩
    have hden : 0 < (α - 1) * Real.log 2 := mul_pos (sub_pos.mpr hα.1) hlog
    have hsmall : α - 1 < δ := by linarith
    have hprod : (α - 1) * ((L - S) * Real.log 2) < 2 * γ :=
      (lt_div_iff₀ (mul_pos hSL hlog)).mp hsmall
    have hc : L - S ≤ 2 * γ / ((α - 1) * Real.log 2) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith
    linarith

/-- The quantitative max-bound implies every strict upper neighborhood of the Umegaki rate. -/
theorem eventually_lt_of_exponential_bounds (f : ℝ → EReal) (d : ℝ)
    (hupper : ∀ S : ℝ, d < S → ∃ L γ : ℝ, 0 < γ ∧
      ∀ α : ℝ, 1 < α → α ≤ 2 →
        f α ≤ (max S (L - 2 * γ / ((α - 1) * Real.log 2)) : ℝ))
    (b : EReal) (hb : (d : EReal) < b) :
    ∀ᶠ α : ℝ in 𝓝[>] (1 : ℝ), f α < b := by
  obtain ⟨S, hdS, hSb⟩ := EReal.exists_between_coe_real hb
  obtain ⟨L, γ, hγ, hbound⟩ := hupper S (EReal.coe_lt_coe_iff.mp hdS)
  filter_upwards [eventually_correction_le S L γ hγ] with α hα
  have h := hbound α hα.1 hα.2.1
  rw [max_eq_left hα.2.2] at h
  exact h.trans_lt hSb

/-- Genuine lower bounds plus the quantitative estimates give the full right limit. -/
theorem tendsto_right_of_exponential_bounds (f : ℝ → EReal) (d : ℝ)
    (hlower : ∀ᶠ α : ℝ in 𝓝[>] (1 : ℝ), (d : EReal) ≤ f α)
    (hupper : ∀ S : ℝ, d < S → ∃ L γ : ℝ, 0 < γ ∧
      ∀ α : ℝ, 1 < α → α ≤ 2 →
        f α ≤ (max S (L - 2 * γ / ((α - 1) * Real.log 2)) : ℝ)) :
    Tendsto f (𝓝[>] (1 : ℝ)) (𝓝 (d : EReal)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hlower] with α hα
    exact ha.trans_le hα
  · intro b hb
    exact eventually_lt_of_exponential_bounds f d hupper b hb

end QuantumChannelStein.RenyiExponentialScalars
