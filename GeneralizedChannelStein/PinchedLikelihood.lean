import GeneralizedChannelStein.PinchingEntropy
import GeneralizedChannelStein.CommutingLikelihood

/-! # A finite quantum large-error test with the exact spectral overhead -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.PinchedLikelihood
open QuantumChannelStein QuantumChannelStein.RelativeEntropy Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Any effect respects actual positive-semidefinite domination. -/
theorem probability_le_of_domination (Q : Effect n) (ρ σ : State n) (c : ℝ)
    (h : (c • σ.matrix - ρ.matrix).PosSemidef) : Q.probability ρ ≤ c * Q.probability σ := by
  have hh := (Complex.nonneg_iff.mp (trace_mul_nonnegative Q.positive h)).1
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul] at hh
  exact sub_nonneg.mp hh

/-- The literal finite-state bound used by Lemma 33, before a hardest-alternative choice. -/
theorem exists_large_error_effect (ρ σ σ₀ : State n) (E L ε v : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hEL : E-Real.logb 2 v < L)
    (hv : (Fintype.card (SpectralPinching.Block σ) : ℝ) ≤ v)
    (hdom : (((2 : ℝ)^L) • σ.matrix - ρ.matrix).PosSemidef)
    (hσ₀ : ((2 : ℝ) • σ.matrix - σ₀.matrix).PosSemidef)
    (hE : E ≤ traceFormula ρ σ) :
    ∃ Q : Effect n, 1-ε ≤ Q.probability ρ ∧
      Q.probability σ₀ ≤ 2 * (2 : ℝ)^(-((E-Real.logb 2 v-(1-ε)*L)/ε)) := by
  let P := SpectralPinching.channel σ
  let ρ' := P.onState ρ
  have hσ : P.onState σ = σ := SpectralPinching.channel_onState_sigma σ
  have hdp : (((2 : ℝ)^L) • σ.matrix - ρ'.matrix).PosSemidef := by
    have hh := P.apply_positive hdom
    change (P.toLinearMap (((2 : ℝ)^L) • σ.matrix - ρ.matrix)).PosSemidef at hh
    rw [map_sub, LinearMap.map_smul_of_tower] at hh
    change (((2 : ℝ)^L) • (SpectralPinching.channel σ).apply σ.matrix - ρ'.matrix).PosSemidef at hh
    rwa [SpectralPinching.channel_fixes_sigma] at hh
  have hcard : 0 < (Fintype.card (SpectralPinching.Block σ) : ℝ) := by
    have hn := MatrixOperatorBridge.state_dimension_pos σ
    have hc : Nonempty (SpectralPinching.Block σ) := ⟨SpectralPinching.eigenvalueIndex σ ⟨0,hn⟩⟩
    exact_mod_cast Fintype.card_pos_iff.mpr hc
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hcard hv
  have hE' : E-Real.logb 2 v ≤ traceFormula ρ' σ := by
    have hh := PinchingEntropy.traceFormula_pinching_loss ρ σ
    change traceFormula ρ σ - _ ≤ traceFormula ρ' σ at hh
    linarith
  obtain ⟨Q,hQ,hcost⟩ := CommutingLikelihood.exists_threshold_effect ρ' σ
    (E-Real.logb 2 v) L ε hε hε1 hEL
    (SpectralPinching.channel_apply_commutes σ ρ.matrix).symm hdp hE'
  refine ⟨P.pullbackEffect Q, ?_, ?_⟩
  · rw [KrausChannel.pullbackEffect_probability]
    exact hQ
  · have hh := probability_le_of_domination (P.pullbackEffect Q) σ₀ σ 2 hσ₀
    rw [KrausChannel.pullbackEffect_probability P Q σ, hσ] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hcost (by norm_num))

end GeneralizedChannelStein.PinchedLikelihood
