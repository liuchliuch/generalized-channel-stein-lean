import GeneralizedChannelStein.CompletionComponents
import GeneralizedChannelStein.CompletionLossScalars
import GeneralizedChannelStein.StatePreserving
import GeneralizedChannelStein.QuantitativeCompletion

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.PaperSpecializations
open QuantumChannelStein Filter PerfectDiscrimination OperationalTesting DiamondNorm
open scoped Topology ComplexOrder

def polynomialRadius (q : ℝ) (n : ℕ) : ℝ := (1/16)*((n:ℝ)+1)^(-q)

theorem polynomialRadius_pos (q : ℝ) (n : ℕ) : 0<polynomialRadius q n := by
  unfold polynomialRadius
  positivity

theorem polynomialRadius_le (q : ℝ) (hq : 0≤q) (n : ℕ) : polynomialRadius q n≤1/16 := by
  have h := Real.rpow_le_one_of_one_le_of_nonpos
    (show (1:ℝ)≤(n:ℝ)+1 by have := Nat.cast_nonneg (α:=ℝ) n; linarith) (neg_nonpos.mpr hq)
  unfold polynomialRadius
  nlinarith

theorem polynomial_loss_bound (K q : ℝ) (hK : 0≤K) (_hq : 0≤q)
    (n : ℕ) (hn : 0<n) :
    completionLoss K n (polynomialRadius q n) ≤ K*(q+5)*CompletionLossScalars.lossScale n := by
  have hx : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hl : 1≤Real.logb 2 ((n:ℝ)+1) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤(n:ℝ)+1 by
        have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
        linarith)
    simpa only [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using h
  have h16 : Real.logb 2 (1/16:ℝ) = -4 := by
    have h := Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1) (x:=(-4:ℝ))
    norm_num at h ⊢
    exact h
  have hlog : Real.logb 2 (((n:ℝ)+1)/polynomialRadius q n) =
      (q+1)*Real.logb 2 ((n:ℝ)+1)+4 := by
    rw [Real.logb_div hx.ne' (polynomialRadius_pos q n).ne']
    unfold polynomialRadius
    rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hx _).ne',
      Real.logb_rpow_eq_mul_logb_of_pos hx, h16]
    ring
  unfold completionLoss CompletionLossScalars.lossScale
  rw [hlog]
  have hm : 0≤K*(n:ℝ)^((2:ℝ)/3) := by positivity
  have hh := mul_le_mul_of_nonneg_left (show (q+1)*Real.logb 2 ((n:ℝ)+1)+4 ≤
    (q+5)*Real.logb 2 ((n:ℝ)+1) by nlinarith) hm
  convert hh using 1; ring

theorem polynomial_loss_tendsto_zero (K q : ℝ) (hK : 0≤K) (hq : 0≤q) :
    Tendsto (fun n : ℕ => completionLoss K n (polynomialRadius q n)/(n:ℝ)) atTop (𝓝 0) := by
  have h := CompletionLossScalars.normalized_loss_tendsto_zero.const_mul (K*(q+5))
  simp only [mul_zero] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [] with n
    exact div_nonneg (CompletionComponents.loss_nonneg K hK n _
      (polynomialRadius_pos q n) (polynomialRadius_le q hq n)) (Nat.cast_nonneg n)
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
      (polynomial_loss_bound K q hK hq n hn) (Nat.cast_nonneg n)

/-- The unique input state in dimension one. -/
def scalarState : State 1 := ⟨1, Matrix.PosSemidef.one, by simp⟩

theorem scalar_matrix (X : Operator 1) : X = X.trace • (1:Operator 1) := by
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  simp [Matrix.trace, Matrix.diag]

theorem channel_one_replacer {b : ℕ} (M : KrausChannel 1 b) :
    M.toLinearMap = (ReplacerChannel.channel 1 (M.onState scalarState)).toLinearMap := by
  ext X i j
  have h := congrArg M.toLinearMap (scalar_matrix X)
  rw [map_smul] at h
  change M.apply X = X.trace • (M.onState scalarState).matrix at h
  change M.apply X i j = (ReplacerChannel.channel 1 (M.onState scalarState)).apply X i j
  rw [ReplacerChannel.channel_apply]
  exact congrFun (congrFun h i) j

def singletonFamily {a b : ℕ} (M : KrausChannel a b) : AlternativeFamily a b :=
  fun n => {(M.tensorPower n).toLinearMap}

theorem singleton_faithful_replacer {a b : ℕ} (M : KrausChannel a b)
    (hF : ∃ω : State b, ω.matrix.PosDef ∧
      ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ singletonFamily M 1) :
    ∃ω : State b, ω.matrix.PosDef ∧ M.toLinearMap = (ReplacerChannel.channel a ω).toLinearMap := by
  obtain ⟨ω,hω,hm⟩ := hF
  change ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap = (M.tensorPower 1).toLinearMap at hm
  refine ⟨ω,hω,?_⟩
  have cast_congr {u v u' v' : ℕ} (U V : KrausChannel u v)
      (hu : u=u') (hv : v=v') (h : U.toLinearMap=V.toLinearMap) :
      (U.cast hu hv).toLinearMap=(V.cast hu hv).toLinearMap := by
    cases hu; cases hv; exact h
  have hc := cast_congr _ _ (Nat.pow_one a) (Nat.pow_one b) hm
  simpa only [KrausChannel.tensorPower_one_toLinearMap] using hc.symm

/-- The polynomial-radius weights differ from the optimal testing exponent by o(n). -/
theorem polynomial_component_gap {a b : ℕ} (N : KrausChannel a b)
    (ha : 0<a) (hb : 0<b) (F : AlternativeFamily a b) (hF : Admissible F)
    (ε K q : ℝ) (hε : 0<ε) (hε1 : ε<1) (hK : 0≤K) (hq : 0≤q) :
    Tendsto (fun n : ℕ =>
      (-Real.logb 2 ((compositeBeta (N.tensorPower n) (F n) ε).toReal *
        (2:ℝ)^(-completionLoss K n (polynomialRadius q n))) +
       Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal)/(n:ℝ))
      atTop (𝓝 0) := by
  apply (polynomial_loss_tendsto_zero K q hK hq).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hf := admissible_values_finite N ha hb F hF n hn ε hε hε1
  have hp := ENNReal.toReal_pos hf.2.2.1.ne' hf.2.2.2.ne
  rw [Real.logb_mul hp.ne' (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne',
    Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)]
  ring

theorem singleton_admissible_replacer {a b : ℕ} (M : KrausChannel a b)
    (hF : Admissible (singletonFamily M)) :
    ∃ω : State b, ω.matrix.PosDef ∧ M.toLinearMap = (ReplacerChannel.channel a ω).toLinearMap :=
  singleton_faithful_replacer M hF.faithful_replacer

/-- All normalized output states occur, and their representing map is unique. -/
theorem channel_one_classification {b : ℕ} (Φ : MatrixMap 1 b) :
    IsChannel Φ ↔ ∃!ρ : State b, Φ=(ReplacerChannel.channel 1 ρ).toLinearMap := by
  constructor
  · intro h
    obtain ⟨M,rfl⟩ := (isChannel_iff_kraus Φ).mp h
    refine ⟨M.onState scalarState,channel_one_replacer M,?_⟩
    intro ρ hρ
    apply State.eq_of_matrix_eq
    have hh := congrArg (fun f : MatrixMap 1 b => f scalarState.matrix)
      (hρ.symm.trans (channel_one_replacer M))
    change (ReplacerChannel.channel 1 ρ).apply scalarState.matrix =
      (ReplacerChannel.channel 1 (M.onState scalarState)).apply scalarState.matrix at hh
    simpa only [ReplacerChannel.channel_apply,scalarState.trace_one,one_smul] using hh
  · rintro ⟨ρ,rfl,_⟩
    exact (isChannel_iff_kraus _).mpr ⟨_,rfl⟩

/-- A single state effect represents a channel tester uniformly over every channel. -/
theorem channel_one_testing {b : ℕ} (t : ChannelTest 1 b) :
    ∃T : Effect b, ∀M : KrausChannel 1 b,
      T.probability (M.onState scalarState)=t.acceptance M := by
  obtain ⟨T,hT⟩ := exists_replacer_effect t
  refine ⟨T,fun M => ?_⟩
  rw [hT,← channelTest_acceptance_congr (channel_one_replacer M)]

/-- Every state effect also defines exactly that channel test. -/
theorem state_effect_channel_test {b : ℕ} (T : Effect b) (M : KrausChannel 1 b) :
    (unassistedTest scalarState T).acceptance M = T.probability (M.onState scalarState) :=
  unassistedTest_acceptance scalarState T M

theorem channel_one_entropy {b : ℕ} (N M : KrausChannel 1 b) :
    ChannelEntropy.channelD N M = RelativeEntropy.umegaki (N.onState scalarState) (M.onState scalarState) := by
  rw [ChannelEntropy.channelD_congr N _ M _ (channel_one_replacer N) (channel_one_replacer M)]
  exact ReplacerChannel.channelD_eq _ _ (by norm_num)

/-- Actual normalized channel components exist at every polynomial radius, with one K. -/
theorem polynomial_completion {a b : ℕ} (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ∃K : ℝ, 0≤K ∧ ∀q : ℝ, 0≤q →
      (Tendsto (fun n : ℕ => completionLoss K n (polynomialRadius q n)/(n:ℝ)) atTop (𝓝 0)) ∧
      ∀n : ℕ, 0<n →
      let p := (compositeBeta (N.tensorPower n) (F n) ε).toReal *
        (2:ℝ)^(-completionLoss K n (polynomialRadius q n))
      0<p ∧ p<1 ∧ ∃L S Q : KrausChannel (a^n) (b^n), S.toLinearMap∈F n ∧
        S.toLinearMap=Complex.ofReal p • L.toLinearMap+Complex.ofReal (1-p) • Q.toLinearMap ∧
        diamondNorm (L.toLinearMap-(N.tensorPower n).toLinearMap)≤ENNReal.ofReal (polynomialRadius q n) := by
  obtain ⟨K,hK⟩ := theorem_16_exists N ha hb F hF hQ ε hε hε1
  refine ⟨K,hK.constant_nonneg,fun q hq => ⟨polynomial_loss_tendsto_zero K q hK.constant_nonneg hq,?_⟩⟩
  intro n hn
  exact CompletionComponents.completion_decomposition N ha hb F hF ε K hε hε1 hK n hn _
    (polynomialRadius_pos q n) (polynomialRadius_le q hq n)

/-- Any eventually larger accuracy tolerance has the same sublinear completion loss. -/
theorem polynomially_bounded_loss {K q : ℝ} (hK : 0≤K) (hq : 0≤q)
    (δ : ℕ→ℝ) (hδ : ∀ᶠn in atTop, polynomialRadius q n≤δ n ∧ δ n≤1/16) :
    Tendsto (fun n : ℕ => completionLoss K n (δ n)/(n:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (polynomial_loss_tendsto_zero K q hK hq)
  · filter_upwards [hδ] with n hn
    exact div_nonneg (CompletionComponents.loss_nonneg K hK n _
      ((polynomialRadius_pos q n).trans_le hn.1) hn.2) (Nat.cast_nonneg n)
  · filter_upwards [hδ] with n hn
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    unfold completionLoss
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.logb_le_logb_of_le (by norm_num)
      (div_pos (by positivity) ((polynomialRadius_pos q n).trans_le hn.1))
    exact div_le_div_of_nonneg_left (by positivity) (polynomialRadius_pos q n) hn.1

end GeneralizedChannelStein.PaperSpecializations
