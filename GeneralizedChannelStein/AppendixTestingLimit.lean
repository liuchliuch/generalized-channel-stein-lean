import GeneralizedChannelStein.TensorDiamond
import GeneralizedChannelStein.QuantitativeConsequences
import GeneralizedChannelStein.NearSubadditive
import GeneralizedChannelStein.AppendixEntropyIdentification
import GeneralizedChannelStein.AppendixCompletionScalars

/-! The completion-based alternative testing-limit proof from Appendix B. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.AppendixTestingLimit
open QuantumChannelStein ChannelEntropy DiamondNorm ChannelPowerReindex
open scoped ComplexOrder Topology
variable {a b : ℕ}

theorem tensorBlocks_component (n m : ℕ)
    (L S : KrausChannel (a^n) (b^n)) (L' S' : KrausChannel (a^m) (b^m))
    (w w' : ℝ) (hw : 0≤w) (hw' : 0≤w')
    (h : MatrixMap.CPLe ((w:ℂ) • L.toLinearMap) S.toLinearMap)
    (h' : MatrixMap.CPLe ((w':ℂ) • L'.toLinearMap) S'.toLinearMap) :
    MatrixMap.CPLe (((w*w':ℝ):ℂ) • (tensorBlocks n m L L').toLinearMap)
      (tensorBlocks n m S S').toLinearMap := by
  have ht := MatrixMap.cpLe_tensor
    (MatrixMap.completelyPositive_smul hw (MatrixMap.completelyPositive_toLinearMap L))
    (MatrixMap.completelyPositive_toLinearMap S') h h'
  simp only [MatrixMap.tensor_smul_left, MatrixMap.tensor_smul_right, smul_smul,
    ← Complex.ofReal_mul, MatrixMap.tensor_kraus_toLinearMap] at ht
  have hr := TensorDiamond.cpLe_reindexMap (channelAddEquiv a n m) (channelAddEquiv b n m) ht
  simpa only [TensorDiamond.reindexMap_smul, TensorDiamond.reindexMap_channel, tensorBlocks, mul_comm w' w] using hr

/-- Actual completion witnesses multiply, with a full diamond estimate on the joint block. -/
theorem completed_product (N : KrausChannel a b) (F : AlternativeFamily a b)
    (hF : Admissible F) (K : ℝ) (hc : CompletionProperty N F (1/2) K)
    (n m : ℕ) (hn : 0<n) (hm : 0<m) :
    ∃ L S : KrausChannel (a^(n+m)) (b^(n+m)), S.toLinearMap∈F (n+m) ∧
      MatrixMap.CPLe
        (((((compositeBeta (N.tensorPower n) (F n) (1/2)).toReal *
          (2:ℝ)^(-completionLoss K n (1/16))) *
          ((compositeBeta (N.tensorPower m) (F m) (1/2)).toReal *
          (2:ℝ)^(-completionLoss K m (1/16))) : ℝ) : ℂ) • L.toLinearMap)
        S.toLinearMap ∧
      diamondNorm (L.toLinearMap-(N.tensorPower (n+m)).toLinearMap) ≤ ENNReal.ofReal (1/8) := by
  obtain ⟨L,S,hS,hord,hclose⟩ := hc.complete n hn (1/16) (by norm_num) le_rfl
  obtain ⟨L',S',hS',hord',hclose'⟩ := hc.complete m hm (1/16) (by norm_num) le_rfl
  refine ⟨tensorBlocks n m L L',tensorBlocks n m S S',
    hF.tensor_closed n m hn hm S S' hS hS',?_,?_⟩
  · exact tensorBlocks_component n m L S L' S' _ _ (by positivity) (by positivity) hord hord'
  · have ht := TensorDiamond.tensorBlocks_difference_le n m L (N.tensorPower n) L' (N.tensorPower m)
    simp only [tensorBlocks,tensorPower_add_toLinearMap] at ht
    exact ht.trans ((add_le_add hclose hclose').trans (by rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num))

/-- Near-subadditivity follows from actual tensor witnesses and entangled-input diamond control. -/
theorem exponent_near_subadditive (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (K : ℝ) (hc : CompletionProperty N F (1/2) K)
    (n m : ℕ) (hn : 0<n) (hm : 0<m) :
    ToleranceComparison.exponent N F (1/2) (n+m) ≤
      ToleranceComparison.exponent N F (1/2) n+ToleranceComparison.exponent N F (1/2) m+
      completionLoss K n (1/16)+completionLoss K m (1/16)+2 := by
  obtain ⟨L,S,hS,hord,hclose⟩ := completed_product N F hF K hc n m hn hm
  have hbn := (admissible_values_finite N ha hb F hF n hn (1/2) (by norm_num) (by norm_num)).2.2
  have hbm := (admissible_values_finite N ha hb F hF m hm (1/2) (by norm_num) (by norm_num)).2.2
  have hpn := ENNReal.toReal_pos hbn.1.ne' hbn.2.ne
  have hpm := ENNReal.toReal_pos hbm.1.ne' hbm.2.ne
  let w : ℝ := ((compositeBeta (N.tensorPower n) (F n) (1/2)).toReal *
    (2:ℝ)^(-completionLoss K n (1/16))) *
    ((compositeBeta (N.tensorPower m) (F m) (1/2)).toReal *
    (2:ℝ)^(-completionLoss K m (1/16)))
  have hw : 0<w := by dsimp [w]; positivity
  have hdom := CompletionConsequences.cpLe_of_component L S w hw hord
  have hcost : 1≤w⁻¹ := one_le_domination_constant _ _ L.trace_apply S.trace_apply
    (PureReferenceRecovery.inputDensity (unitProductInput (pow_pos ha (n+m)))) hdom
  have hup := smoothedResourceMax_le_of_witness (N.tensorPower (n+m)) L S (F (n+m)) hS
    w⁻¹ (1/2) hcost hdom (hclose.trans (ENNReal.ofReal_le_ofReal (by norm_num)))
  have hlo := CompletionConsequences.smoothing_lower N ha hb F hF (1/2)
    (by norm_num) (by norm_num) (n+m) (by omega) (1/2) (by norm_num) (by norm_num)
  have hlog : Real.logb 2 w⁻¹ = ToleranceComparison.exponent N F (1/2) n+
      ToleranceComparison.exponent N F (1/2) m+
      completionLoss K n (1/16)+completionLoss K m (1/16) := by
    rw [Real.logb_inv]
    dsimp [w, ToleranceComparison.exponent]
    rw [Real.logb_mul (mul_pos hpn (Real.rpow_pos_of_pos (by norm_num) _)).ne'
      (mul_pos hpm (Real.rpow_pos_of_pos (by norm_num) _)).ne',
      Real.logb_mul hpn.ne' (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne',
      Real.logb_mul hpm.ne' (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne',
      Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1),
      Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)]
    ring
  have hquarter : Real.logb 2 (1-(1/2:ℝ)-(1/2)/2) = -2 := by
    have hh : Real.logb 2 ((2:ℝ)^(-2:ℝ)) = -2 := Real.logb_rpow (by norm_num) (by norm_num)
    norm_num at hh ⊢
    exact hh
  have hh := EReal.coe_le_coe_iff.mp (hlo.trans hup)
  rw [hlog, hquarter] at hh
  dsimp [ToleranceComparison.exponent] at *
  linarith

theorem half_exponent_bounds (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (n : ℕ) (hn : 0<n) :
    0≤ToleranceComparison.exponent N F (1/2) n ∧
    ToleranceComparison.exponent N F (1/2) n≤(2*replacerRate ω hb)*n+2 := by
  have h := lemma_4 N ha hb F hF ω hω hOne n hn (1/2) (by norm_num) (by norm_num)
  have hf := admissible_values_finite N ha hb F hF n hn (1/2) (by norm_num) (by norm_num)
  have hbR := ENNReal.toReal_mono ENNReal.ofReal_ne_top h.2.1.2
  rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1-1/2)] at hbR
  have hl := Real.logb_nonpos (by norm_num : (1:ℝ)<2)
    (ENNReal.toReal_nonneg : 0≤(compositeBeta (N.tensorPower n) (F n) (1/2)).toReal)
    (hbR.trans (by norm_num))
  have he : (familyEntropy (N.tensorPower n) (F n)).toReal≤(n:ℝ)*replacerRate ω hb := by
    have hh := h.1.2
    rw [← EReal.coe_toReal hf.1 hf.2.1] at hh
    exact EReal.coe_le_coe_iff.mp hh
  dsimp [ToleranceComparison.exponent]
  constructor
  · linarith
  · nlinarith [h.2.2]

/-- Conditional scalar-envelope assembly; the final endpoint supplies this envelope explicitly. -/
theorem common_testing_limit_of_envelope (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F)
    (K C : ℝ) (hc : CompletionProperty N F (1/2) K) (hC : 0≤C)
    (hbound : ∀ n m : ℕ, 0<n → 0<m →
      completionLoss K n (1/16)+completionLoss K m (1/16)+2≤C*((n+m:ℕ):ℝ)^((5:ℝ)/6)) :
    ∃ R : ℝ, 0≤R ∧ ∀ ε : ℝ, 0<ε → ε<1 →
      Filter.Tendsto (testingRateReal N F ε) Filter.atTop (𝓝 R) := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  have hbs := half_exponent_bounds N ha hb F hF ω hω hOne
  obtain ⟨R,hR0,hR⟩ := NearSubadditive.exists_limit_of_power_error hC
    (by norm_num : (0:ℝ)<5/6) (by norm_num : (5:ℝ)/6<1)
    (fun n hn => (hbs n hn).1) (fun n hn => (hbs n hn).2)
    (fun n m hn hm => (exponent_near_subadditive N ha hb F hF K hc n m hn hm).trans
      (by linarith [hbound n m hn hm]))
  refine ⟨R,hR0,?_⟩
  intro ε hε hε1
  have hd := lemma_18_normalized N ha hb F hF hQ ε (1/2) hε hε1 (by norm_num) (by norm_num)
  have hs := hd.add hR
  rw [zero_add] at hs
  apply hs.congr'
  filter_upwards [] with n
  dsimp [testingRateReal, ToleranceComparison.exponent]
  ring

/-- Complete independent Appendix B route once the elementary overhead envelope is supplied. -/
theorem appendix_common_limit_of_completion_envelope (N : KrausChannel a b)
    (ha : 0<a) (hb : 0<b) (F : AlternativeFamily a b)
    (hF : Admissible F) (hQ : QuantitativeConditions F)
    (K C : ℝ) (hc : CompletionProperty N F (1/2) K) (hC : 0≤C)
    (hbound : ∀ n m : ℕ, 0<n → 0<m →
      completionLoss K n (1/16)+completionLoss K m (1/16)+2≤C*((n+m:ℕ):ℝ)^((5:ℝ)/6)) :
    ∃ R : ℝ, 0≤R ∧
      (∀ ε : ℝ, 0<ε → ε<1 → Filter.Tendsto (testingRateReal N F ε) Filter.atTop (𝓝 R)) ∧
      Filter.Tendsto (entropyRateReal N F) Filter.atTop (𝓝 R) ∧
      (∀ ω : State b, ω.matrix.PosDef →
        ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1 → R≤replacerRate ω hb) := by
  obtain ⟨R,hR0,hR⟩ := common_testing_limit_of_envelope N ha hb F hF hQ K C hc hC hbound
  obtain ⟨τ,hτ⟩ := hQ
  refine ⟨R,hR0,hR,
    AppendixEntropyIdentification.entropy_limit_of_common_testing_limit N ha hb F hF
      hτ.permutation_closed R hR,?_⟩
  intro ω hω hOne
  exact (AppendixEntropyIdentification.common_rate_bounds N ha hb F hF
    hτ.permutation_closed R hR ω hω hOne).2

/-- Appendix B's alternative proof of Theorem 2 under F1–F5, with no main-limit oracle.
The completion radius is fixed at 1/16; its overhead remains sublinear. -/
theorem appendix_b_theorem_2 (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F) :
    ∃ R : ℝ, 0≤R ∧
      (∀ ε : ℝ, 0<ε → ε<1 → Filter.Tendsto (testingRateReal N F ε) Filter.atTop (𝓝 R)) ∧
      Filter.Tendsto (entropyRateReal N F) Filter.atTop (𝓝 R) ∧
      (∀ ω : State b, ω.matrix.PosDef →
        ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1 → R≤replacerRate ω hb) := by
  obtain ⟨K,hK⟩ := theorem_16_exists N ha hb F hF hQ (1/2) (by norm_num) (by norm_num)
  obtain ⟨C,hC,hbound⟩ := AppendixCompletionScalars.exists_fixed_radius_envelope K hK.constant_nonneg
  exact appendix_common_limit_of_completion_envelope N ha hb F hF hQ K C hK hC hbound

end GeneralizedChannelStein.AppendixTestingLimit
