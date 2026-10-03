import GeneralizedChannelStein.LocalTruncation
import GeneralizedChannelStein.LocalExpansionCompact
import GeneralizedChannelStein.UnitaryConcentration
import GeneralizedChannelStein.InvariantIntegral

/-! Explicit measurable good-unitary integrands and literal local-expansion budgets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.GoodUnitaryIntegrand
open QuantumChannelStein Matrix MeasureTheory LocalExpansion LocalTruncation InvariantIntegral
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {d : ℕ}

local instance operatorMeasurableSpace : MeasurableSpace (Operator d) := borel _
local instance operatorBorelSpace : BorelSpace (Operator d) := ⟨rfl⟩
local instance blockMeasurableSpace (k : ℕ) : MeasurableSpace (Block (Fin d) k) := borel _
local instance blockBorelSpace (k : ℕ) : BorelSpace (Block (Fin d) k) := ⟨rfl⟩

def expectation (τ : State d) (U : UnitaryGroup d) : ℂ := (τ.matrix*U.val).trace
def phase (τ : State d) (U : UnitaryGroup d) : ℂ := expectation τ U / (‖expectation τ U‖:ℂ)
def goodSet (τ : State d) (t u : ℝ) : Set (UnitaryGroup d) :=
  {U | 1-t*u^2/2 ≤ ‖expectation τ U‖}

def integrand (τ : State d) (t u : ℝ) (f : UnitaryGroup d → ℂ) (m k R : ℕ)
    (U : UnitaryGroup d) : Block (Fin d) k := by
  classical
  exact if U∈goodSet τ t u then (f U * expectation τ U ^ m) • phaseTruncation U.val (phase τ U) k R else 0

theorem continuous_expectation (τ : State d) : Continuous (expectation τ) := by
  unfold expectation
  exact (continuous_const.mul continuous_subtype_val).matrix_trace

theorem measurable_phase (τ : State d) : Measurable (phase τ) := by
  have he := (continuous_expectation τ).measurable
  unfold phase
  fun_prop

theorem measurable_goodSet (τ : State d) (t u : ℝ) : MeasurableSet (goodSet τ t u) :=
  (isClosed_le continuous_const (continuous_expectation τ).norm).measurableSet

theorem measurable_integrand (τ : State d) (t u : ℝ) (f : UnitaryGroup d → ℂ)
    (hf : Measurable f) (m k R : ℕ) : Measurable (integrand τ t u f m k R) := by
  classical
  have hp := (measurable_phaseTruncation (ι := Fin d) k R).comp
    (continuous_subtype_val.measurable.prodMk (measurable_phase τ))
  have he := (continuous_expectation τ).measurable
  unfold integrand
  apply Measurable.ite (measurable_goodSet τ t u)
  · exact (hf.mul (he.pow_const m)).smul hp
  · exact measurable_const

theorem good_phase_parameters (τ : State d) (t u : ℝ) (ht : 0<t) (ht1 : t≤1)
    (hu : 0≤u) (hu1 : u<1) (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (U : UnitaryGroup d) (hgood : U∈goodSet τ t u) :
    ‖phase τ U‖=1 ∧ ‖U.val-phase τ U • (1:Operator d)‖≤u := by
  have husq : u^2<1 := by nlinarith
  have htu : t*u^2<1 := by
    have := mul_le_mul_of_nonneg_right ht1 (sq_nonneg u)
    nlinarith
  have hp : 0<‖expectation τ U‖ := by
    change 1-t*u^2/2≤‖expectation τ U‖ at hgood
    linarith
  have hn : expectation τ U ≠ 0 := norm_ne_zero_iff.mp hp.ne'
  exact ⟨normalized_phase_norm _ hn,
    good_unitary_near_phase τ t u ht hu hτ U hgood hn⟩

theorem amplitude_norm_le (τ : State d) (f : UnitaryGroup d → ℂ) (v : ℝ)
    (hv : ∀ U, ‖f U‖≤v) (m : ℕ) (U : UnitaryGroup d) :
    ‖f U*expectation τ U ^ m‖≤v := by
  rw [norm_mul,norm_pow]
  have he : ‖expectation τ U‖^m≤1 := pow_le_one₀ (norm_nonneg _) (state_unitary_trace_norm_le_one τ U)
  exact (mul_le_of_le_one_right (norm_nonneg _) he).trans (hv U)

theorem norm_expansion_value_le_cost {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} (E : Expansion ι k) : ‖E.value‖≤E.cost := by
  unfold Expansion.value Expansion.cost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (E.contraction i)

theorem integrand_has_expansion [NeZero d] (τ : State d) (t u : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hu : 0≤u) (hu1 : u<1)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (f : UnitaryGroup d → ℂ) (v : ℝ) (hv : 0≤v) (hf : ∀ U, ‖f U‖≤v)
    (m k R : ℕ) (U : UnitaryGroup d) :
    ∃ E : Expansion (Fin d) k, E.value=integrand τ t u f m k R U ∧
      E.HasSize R ∧ E.cost≤v*Real.exp ((k:ℝ)*u) := by
  classical
  by_cases hgood : U∈goodSet τ t u
  · obtain ⟨hz,hclose⟩ := good_phase_parameters τ t u ht ht1 hu hu1 hτ U hgood
    let E := phaseExpansion U.val (phase τ U) u hz hclose k R
    let a := f U*expectation τ U^m
    refine ⟨E.scale a, ?_, Expansion.hasSize_scale E (phaseExpansion_size _ _ _ _ _ _ _) a, ?_⟩
    · simp [E,a,integrand,hgood,phaseExpansion_value]
    · rw [Expansion.cost_scale]
      have hc : E.cost≤Real.exp ((k:ℝ)*u) := phaseExpansion_cost _ _ _ _ _ _ _
      have ha : ‖a‖≤v := amplitude_norm_le τ f v hf m U
      exact mul_le_mul ha hc (Expansion.cost_nonneg E) hv
  · let E := (Expansion.one (ι := Fin d) (k := k)).scale 0
    refine ⟨E, ?_, Expansion.hasSize_scale _ (Expansion.hasSize_one R) 0, ?_⟩
    · simp [E,integrand,hgood]
    · simp only [E,Expansion.cost_scale,norm_zero,zero_mul]
      positivity

theorem norm_integrand_le [NeZero d] (τ : State d) (t u : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hu : 0≤u) (hu1 : u<1)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (f : UnitaryGroup d → ℂ) (v : ℝ) (hv : 0≤v) (hf : ∀ U, ‖f U‖≤v)
    (m k R : ℕ) (U : UnitaryGroup d) :
    ‖integrand τ t u f m k R U‖≤v*Real.exp ((k:ℝ)*u) := by
  obtain ⟨E,he,_,hc⟩ := integrand_has_expansion τ t u ht ht1 hu hu1 hτ f v hv hf m k R U
  rw [← he]
  exact (norm_expansion_value_le_cost E).trans hc

theorem integrand_scaled_mem_hull [NeZero d] (τ : State d) (t u : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hu : 0≤u) (hu1 : u<1)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (f : UnitaryGroup d → ℂ) (v : ℝ) (hv : 0<v) (hf : ∀ U, ‖f U‖≤v)
    (m k R : ℕ) (U : UnitaryGroup d) :
    (v*Real.exp ((k:ℝ)*u))⁻¹ • integrand τ t u f m k R U ∈
      convexHull ℝ (localAtoms R) := by
  obtain ⟨E,he,hs,hc⟩ := integrand_has_expansion τ t u ht ht1 hu hu1 hτ f v hv.le hf m k R U
  rw [← he]
  exact expansion_scaled_mem_hull E R hs _ (mul_pos hv (Real.exp_pos _)) hc

theorem integrable_integrand [NeZero d] (τ : State d) (t u : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hu : 0≤u) (hu1 : u<1)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (f : UnitaryGroup d → ℂ) (hf : Continuous f) (v : ℝ)
    (hv : 0≤v) (hfv : ∀ U, ‖f U‖≤v) (m k R : ℕ) :
    Integrable (integrand τ t u f m k R) (haar d) := by
  apply MeasureTheory.Integrable.of_bound
    (measurable_integrand τ t u f hf.measurable m k R).aestronglyMeasurable
    (v*Real.exp ((k:ℝ)*u))
  exact Filter.Eventually.of_forall (norm_integrand_le τ t u ht ht1 hu hu1 hτ f v hv hfv m k R)

/-- The actual Haar average has a finite local contraction expansion. -/
theorem good_integral_has_expansion [NeZero d] (τ : State d) (t u : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hu : 0≤u) (hu1 : u<1)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (f : UnitaryGroup d → ℂ) (hf : Continuous f) (v : ℝ)
    (hv : 0<v) (hfv : ∀ U, ‖f U‖≤v) (m k R : ℕ) :
    ∃ E : Expansion (Fin d) k,
      E.value=(∫ U, integrand τ t u f m k R U ∂haar d) ∧
      E.HasSize R ∧ E.cost≤v*Real.exp ((k:ℝ)*u) := by
  apply exists_expansion_integral (haar d) (integrand τ t u f m k R)
    (integrable_integrand τ t u ht ht1 hu hu1 hτ f hf v hv.le hfv m k R)
    R (v*Real.exp ((k:ℝ)*u)) (mul_pos hv (Real.exp_pos _))
  exact Filter.Eventually.of_forall
    (integrand_scaled_mem_hull τ t u ht ht1 hu hu1 hτ f v hv hfv m k R)

end GeneralizedChannelStein.GoodUnitaryIntegrand
