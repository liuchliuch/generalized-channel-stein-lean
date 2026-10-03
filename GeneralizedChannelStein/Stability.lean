import GeneralizedChannelStein.RealRates
import GeneralizedChannelStein.ApproximationTesting

/-! # Corollary 13: correlated target perturbations in the full diamond norm -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DiamondNorm ParallelExponent Filter
open scoped Topology ComplexOrder
variable {a b : ℕ}

/-- The one-shot tolerance sandwich uses the same input/effect and the same family. -/
theorem perturbation_sandwich (N T : KrausChannel a b) (F : Set (MatrixMap a b))
    (ε u : ℝ) (hu : 0 ≤ u)
    (hclose : diamondNorm (T.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal (2*u)) :
    compositeBeta N F (ε+u) ≤ compositeBeta T F ε ∧
    compositeBeta T F ε ≤ compositeBeta N F (ε-u) := by
  have h1 := compositeBeta_perturbation_lower N T F (2*u) (by linarith) hclose ε
  have hsym : diamondNorm (N.toLinearMap-T.toLinearMap) ≤ ENNReal.ofReal (2*u) := by
    rw [← neg_sub T.toLinearMap N.toLinearMap,diamondNorm_neg]
    exact hclose
  have h2 := compositeBeta_perturbation_lower T N F (2*u) (by linarith) hsym (ε-u)
  constructor
  · convert h1 using 1 <;> congr 1 <;> ring
  · convert h2 using 1 <;> congr 1 <;> ring

/-- **Corollary 13:** the approximating target at each n may have arbitrary
correlations. Only vanishing diamond distance, not an exponential rate, is assumed. -/
theorem corollary_13 (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (T : (n : ℕ) → KrausChannel (a^n) (b^n))
    (hclose : Tendsto (fun n => diamondNorm ((T n).toLinearMap-(N.tensorPower n).toLinearMap))
      atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ => -Real.logb 2 (compositeBeta (T n) (F n) ε).toReal/(n:ℝ))
      atTop (𝓝 (steinRate N F)) := by
  let u := min ε (1-ε)/2
  have hu : 0 < u := div_pos (lt_min hε (sub_pos.mpr hε1)) (by norm_num)
  have hue : u < ε := by dsimp [u]; have := min_le_left ε (1-ε); linarith
  have hue1 : u < 1-ε := by dsimp [u]; have := min_le_right ε (1-ε); linarith
  have hlo : 0 < ε-u := by linarith
  have hlo1 : ε-u < 1 := by linarith
  have hhi : 0 < ε+u := by linarith
  have hhi1 : ε+u < 1 := by linarith
  have hs : ∀ᶠ n : ℕ in atTop,
      compositeBeta (N.tensorPower n) (F n) (ε+u) ≤ compositeBeta (T n) (F n) ε ∧
      compositeBeta (T n) (F n) ε ≤ compositeBeta (N.tensorPower n) (F n) (ε-u) := by
    filter_upwards [hclose.eventually_le_const (ENNReal.ofReal_pos.mpr (by positivity : (0:ℝ)<2*u))]
      with n hn
    exact perturbation_sandwich (N.tensorPower n) (T n) (F n) ε u hu.le hn
  have hexp : Tendsto (fun n => testingExponent n (compositeBeta (T n) (F n) ε))
      atTop (𝓝 (steinRate N F:EReal)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (testing_limit_extended N ha hb F hF (ε-u) hlo hlo1)
      (testing_limit_extended N ha hb F hF (ε+u) hhi hhi1)
      (hs.mono fun n hn => testingExponent_antitone n hn.2)
      (hs.mono fun n hn => testingExponent_antitone n hn.1)
  have hreal := (EReal.tendsto_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).comp hexp
  simp only [EReal.toReal_coe] at hreal
  apply hreal.congr'
  filter_upwards [hs,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  have hpos := (admissible_values_finite N ha hb F hF n hnpos (ε+u) hhi hhi1).2.2.1.trans_le hn.1
  have hfin := hn.2.trans_lt (admissible_values_finite N ha hb F hF n hnpos (ε-u) hlo hlo1).2.2.2
  change (testingExponent n (compositeBeta (T n) (F n) ε)).toReal = _
  rw [testingExponent_eq_real n _ hpos hfin.ne,EReal.toReal_coe]

end GeneralizedChannelStein
