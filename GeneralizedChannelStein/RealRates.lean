import GeneralizedChannelStein.OperationalLimit

/-! # Real normalized rates, only after finiteness has been proved -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter
open scoped Topology ComplexOrder
variable {a b : ℕ}

def testingRateReal (N : KrausChannel a b) (F : AlternativeFamily a b) (ε : ℝ) (n : ℕ) : ℝ :=
  -Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal/(n:ℝ)

def entropyRateReal (N : KrausChannel a b) (F : AlternativeFamily a b) (n : ℕ) : ℝ :=
  (familyEntropy (N.tensorPower n) (F n)).toReal/(n:ℝ)

/-- The paper's ordinary real testing limit, with actual beta finite/positive beforehand. -/
theorem testing_limit (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (testingRateReal N F ε) atTop (𝓝 (steinRate N F)) := by
  have h := (EReal.tendsto_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).comp
    (testing_limit_extended N ha hb F hF ε hε hε1)
  simp only [EReal.toReal_coe] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hf := admissible_values_finite N ha hb F hF n hn ε hε hε1
  change (compositeExponent N F ε n).toReal = _
  rw [compositeExponent, testingExponent_eq_real n _ hf.2.2.1 hf.2.2.2.ne, EReal.toReal_coe]
  rfl

theorem steinRate_le_replacerRate (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1) :
    steinRate N F ≤ replacerRate ω hb := by
  have h := lowerTestingRate_le_replacer N hb F hF ω hω hOne (1/2) (by norm_num)
  rw [← steinRate_coe N ha hb F hF] at h
  exact EReal.coe_le_coe_iff.mp h

/-- Normalized entropy lies in a fixed real interval, including the harmless zero index. -/
theorem entropyRateReal_bounds (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1) (n : ℕ) :
    0 ≤ entropyRateReal N F n ∧ entropyRateReal N F n ≤ replacerRate ω hb := by
  by_cases hn : n = 0
  · subst n
    simp only [entropyRateReal,Nat.cast_zero,div_zero]
    exact ⟨le_rfl,replacerRate_nonneg ω hb hω⟩
  have hnpos := Nat.pos_of_ne_zero hn
  have h := (lemma_4 N ha hb F hF ω hω hOne n hnpos (1/2) (by norm_num) (by norm_num)).1
  have hf := admissible_values_finite N ha hb F hF n hnpos (1/2) (by norm_num) (by norm_num)
  have hE : (familyEntropy (N.tensorPower n) (F n)).toReal ≤ (n:ℝ)*replacerRate ω hb := by
    rw [← EReal.coe_toReal hf.1 hf.2.1] at h
    exact EReal.coe_le_coe_iff.mp h.2
  refine ⟨div_nonneg (EReal.toReal_nonneg h.1) (Nat.cast_nonneg n),?_⟩
  exact (div_le_iff₀ (Nat.cast_pos.mpr hnpos)).mpr (by nlinarith)

/-- The normalized weak converse used to identify the entropy limit. -/
theorem normalized_weak_converse (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (n : ℕ) (hn : 0 < n) :
    (1-ε)*testingRateReal N F ε n-1/(n:ℝ) ≤ entropyRateReal N F n := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  have h := (lemma_4 N ha hb F hF ω hω hOne n hn ε hε hε1).2.2
  have hdiv := div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
  rw [add_div,mul_div_assoc] at hdiv
  dsimp [testingRateReal,entropyRateReal]
  linarith

end GeneralizedChannelStein
