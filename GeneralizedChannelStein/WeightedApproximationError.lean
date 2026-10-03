import GeneralizedChannelStein.WeightedPowerMap
import GeneralizedChannelStein.GoodUnitaryIntegrand
import GeneralizedChannelStein.LocalTruncation
import GeneralizedChannelStein.UnitaryConcentration
import GeneralizedChannelStein.WeightedDiscardingScalars

/-! Genuine pointwise damping and integral error estimates for Lemma 27. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TensorPower MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem damped_power_le_exp (r q h : ℝ) (m : ℕ) (hr : 0 ≤ r)
    (hrq : r ≤ 1-q) (hm : h ≤ m*q) : r^m ≤ Real.exp (-h) := by
  have hbase : r ≤ Real.exp (-q) := by linarith [Real.add_one_le_exp (-q)]
  calc
    r^m ≤ (Real.exp (-q))^m := pow_le_pow_left₀ hr hbase m
    _ = Real.exp (-(m*q)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-h) := Real.exp_le_exp.mpr (by linarith)

/-- The actual damping parameter cancels exactly, with no asymptotic premise. -/
theorem damping_parameter_cancels (t h : ℝ) (m : ℕ) (ht : 0<t) (hm : 0<m) (hh : 0≤h) :
    (m:ℝ)*(t*(Real.sqrt (2*h/(t*m)))^2/2)=h := by
  rw [Real.sq_sqrt (by positivity)]
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  <;> ring

/-- Probability integration preserves a uniform operator error bound. -/
theorem integral_operator_error {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P X : Ω → E)
    (hP : Integrable P μ) (hX : Integrable X μ) (e : ℝ)
    (h : ∀ᵐ x ∂μ, ‖P x-X x‖≤e) :
    ‖(∫ x, P x ∂μ)-(∫ x, X x ∂μ)‖≤e := by
  rw [← integral_sub hP hX]
  simpa using norm_integral_le_of_norm_le_const h

/-- The common pointwise error budget is already below the requested precision. -/
theorem uniform_damping_error_le {d n ξ v : ℝ} (hn : 0 ≤ n) (hξ : 0 < ξ)
    (hξu : ξ ≤ 1/16) (hv : 0 ≤ v)
    (hvb : v ≤ (n+d^2+1) ^ (d^2-1)) :
    v * Real.exp (-WeightedDiscardingScalars.dampingExponent d n ξ) ≤ ξ := by
  have h := WeightedDiscardingScalars.polynomial_damping_error hn hξ hξu hv hvb
  have hp : 0 ≤ 2*v*Real.exp (-2*WeightedDiscardingScalars.dampingExponent d n ξ) := by positivity
  linarith

/-- On the discarded set the damped true unitary tensor is uniformly tiny. -/
theorem bad_unitary_damped_norm {d : ℕ} (τ : State d)
    (U : unitary (Operator d)) (f : ℂ) (v t u h : ℝ) (k m : ℕ)
    (hf : ‖f‖≤v) (hbad : ‖(τ.matrix*(U:Operator d)).trace‖≤1-t*u^2/2)
    (hm : h≤(m:ℝ)*(t*u^2/2)) :
    ‖(f*(τ.matrix*(U:Operator d)).trace^m) • tensorPower (U:Operator d) k‖ ≤
      v*Real.exp (-h) := by
  rw [norm_smul,norm_mul,norm_pow]
  have hp := damped_power_le_exp ‖(τ.matrix*(U:Operator d)).trace‖ (t*u^2/2) h m
    (norm_nonneg _) hbad hm
  have hU := norm_tensorPower_le_one (U:Operator d) (TraceNorm.unitary_opNorm_le_one U) k
  calc
    _ ≤ (‖f‖*‖(τ.matrix*(U:Operator d)).trace‖^m)*1 :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    _ ≤ v*Real.exp (-h) := by
      rw [mul_one]
      exact mul_le_mul hf hp (by positivity) (le_trans (norm_nonneg _) hf)

/-- Both good and bad unitaries satisfy one common error bound. -/
theorem good_integrand_pointwise_error {d : ℕ} [NeZero d] (τ : State d) (t u h v : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hu : 0≤u) (hu1 : u<1) (hh : 0≤h)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (f : InvariantIntegral.UnitaryGroup d → ℂ) (hf : ∀U, ‖f U‖≤v)
    (m k R : ℕ) (hm : h≤(m:ℝ)*(t*u^2/2))
    (hR : Real.exp 2*(k:ℝ)*u+2*h≤(R:ℝ)) (U : InvariantIntegral.UnitaryGroup d) :
    ‖GoodUnitaryIntegrand.integrand τ t u f m k R U -
      (f U*GoodUnitaryIntegrand.expectation τ U^m) • finTensorPower U.val k‖≤v*Real.exp (-h) := by
  classical
  by_cases hg : U∈GoodUnitaryIntegrand.goodSet τ t u
  · obtain ⟨hz,hclose⟩ := GoodUnitaryIntegrand.good_phase_parameters τ t u ht ht1 hu hu1 hτ U hg
    simp only [GoodUnitaryIntegrand.integrand,if_pos hg,← smul_sub,norm_smul]
    have he := LocalTruncation.phaseTruncation_error U.val hz hclose hh k R hR
    rw [norm_sub_rev] at he
    exact mul_le_mul (GoodUnitaryIntegrand.amplitude_norm_le τ f v hf m U) he
      (norm_nonneg _) (le_trans (norm_nonneg _) (hf U))
  · simp only [GoodUnitaryIntegrand.integrand,if_neg hg,zero_sub,norm_neg]
    have hb : ‖(τ.matrix*U.val).trace‖≤1-t*u^2/2 := le_of_lt (lt_of_not_ge hg)
    have he := bad_unitary_damped_norm τ U (f U) v t u h k m (hf U) hb hm
    simpa only [GoodUnitaryIntegrand.expectation,finTensorPower,norm_smul,
      TensorPower.norm_reindex] using he

/-- The explicit truncated Haar average approximates the true damped average. -/
theorem exists_local_expansion_of_density {d : ℕ} [NeZero d]
    (τ : State d) (t u h v : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hu : 0≤u) (hu1 : u<1) (hh : 0≤h) (hv : 0<v)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (f : InvariantIntegral.UnitaryGroup d → ℂ) (hf : Continuous f) (hfv : ∀U, ‖f U‖≤v)
    (m k R : ℕ) (hm : h≤(m:ℝ)*(t*u^2/2))
    (hR : Real.exp 2*(k:ℝ)*u+2*h≤(R:ℝ)) :
    ∃ E : LocalExpansion.Expansion (Fin d) k,
      E.HasSize R ∧ E.cost≤v*Real.exp ((k:ℝ)*u) ∧
      ‖E.value-(∫ U, (f U*GoodUnitaryIntegrand.expectation τ U^m) •
        finTensorPower U.val k ∂InvariantIntegral.haar d)‖≤v*Real.exp (-h) := by
  obtain ⟨E,hE,hs,hc⟩ := GoodUnitaryIntegrand.good_integral_has_expansion τ t u
    ht ht1 hu hu1 hτ f hf v hv hfv m k R
  refine ⟨E,hs,hc,?_⟩
  rw [hE]
  apply integral_operator_error
  · exact GoodUnitaryIntegrand.integrable_integrand τ t u ht ht1 hu hu1 hτ f hf v hv.le hfv m k R
  · have hp : Continuous (fun U : InvariantIntegral.UnitaryGroup d => finTensorPower U.val k) := by
      change Continuous (fun U : InvariantIntegral.UnitaryGroup d => (Matrix.reindexLinearEquiv ℂ ℂ (indexEquiv (Fin d) k)
        (indexEquiv (Fin d) k)) (tensorPower U.val k))
      exact (LinearMap.continuous_of_finiteDimensional _).comp
        (InvariantIntegral.continuous_tensorUnitary_val d k)
    exact ((hf.mul ((GoodUnitaryIntegrand.continuous_expectation τ).pow m)).smul hp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact Filter.Eventually.of_forall
      (good_integrand_pointwise_error τ t u h v ht ht1 hu hu1 hh hτ f hfv m k R hm hR)

end GeneralizedChannelStein
