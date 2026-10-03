import GeneralizedChannelStein.CompletionConsequences
import GeneralizedChannelStein.CompletionLossScalars

/-! # Uniform finite-interval comparison of literal testing exponents -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.ToleranceComparison
open QuantumChannelStein ChannelEntropy CompletionLossScalars Filter
open scoped Topology
variable {a b : ℕ}

/-- The unnormalized actual testing exponent, after the usual positivity proof. -/
def exponent (N : KrausChannel a b) (F : AlternativeFamily a b) (ε : ℝ) (n : ℕ) : ℝ :=
  -Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal

/-- Monotonicity in the error tolerance is proved from the actual feasible test sets. -/
theorem exponent_mono (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (n : ℕ) (hn : 0<n)
    (ε ε' : ℝ) (hε : 0<ε) (hee : ε≤ε') (hε' : ε'<1) :
    exponent N F ε n ≤ exponent N F ε' n := by
  have hf := admissible_values_finite N ha hb F hF n hn ε hε (hee.trans_lt hε')
  have hf' := admissible_values_finite N ha hb F hF n hn ε' (hε.trans_le hee) hε'
  have hβ := compositeBeta_antitone_tolerance (N.tensorPower n) (F n) hee
  have hβR := ENNReal.toReal_mono hf.2.2.2.ne hβ
  exact neg_le_neg (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (ENNReal.toReal_pos hf'.2.2.1.ne' hf'.2.2.2.ne) hβR)

/-- A single completion at the lower endpoint controls the complete interval. -/
theorem endpoint_difference (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (εlo εhi K : ℝ)
    (hεlo : 0<εlo) (hee : εlo≤εhi) (hεhi : εhi<1)
    (hcomp : CompletionProperty N F εlo K)
    (n : ℕ) (hn : 0<n) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1/16)
    (hmargin : 0<1-εhi-δ/2) :
    exponent N F εhi n-exponent N F εlo n ≤ completionLoss K n δ-Real.logb 2 (1-εhi-δ/2) := by
  have hlo := CompletionConsequences.smoothing_lower N ha hb F hF εhi
    (hεlo.trans_le hee) hεhi n hn δ hδ.le hmargin
  have hhi := CompletionConsequences.smoothing_upper N ha hb F hF εlo K
    hεlo (hee.trans_lt hεhi) hcomp n hn δ hδ hδ1
  have h := EReal.coe_le_coe_iff.mp (hlo.trans hhi)
  change exponent N F εhi n + Real.logb 2 (1-εhi-δ/2) ≤
    exponent N F εlo n+completionLoss K n δ at h
  linarith

/-- Uniformity over a closed error interval uses one endpoint completion constant only. -/
theorem uniform_interval_bound (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (εlo εhi K : ℝ)
    (hεlo : 0<εlo) (hee : εlo≤εhi) (hεhi : εhi<1)
    (hcomp : CompletionProperty N F εlo K) :
    ∃ B : ℝ, 0≤B ∧ ∀ n : ℕ, 0<n → ∀ ε∈Set.Icc εlo εhi, ∀ ε'∈Set.Icc εlo εhi,
      |exponent N F ε n-exponent N F ε' n| ≤ B*lossScale n := by
  let δ : ℝ := min (1/16) ((1-εhi)/2)
  let m : ℝ := 1-εhi-δ/2
  have hd : 0<δ := lt_min (by norm_num) (by linarith)
  have hd16 : δ≤1/16 := min_le_left _ _
  have hdε : δ≤(1-εhi)/2 := min_le_right _ _
  have hm : 0<m := by dsimp [m]; linarith
  have hm1 : m≤1 := by dsimp [m]; linarith
  let B : ℝ := K*(1-Real.logb 2 δ)-Real.logb 2 m
  have hδlog : Real.logb 2 δ ≤ 0 := Real.logb_nonpos (by norm_num) hd.le (by linarith)
  have hmlog : Real.logb 2 m ≤ 0 := Real.logb_nonpos (by norm_num) hm.le hm1
  have hB : 0≤B := by
    dsimp [B]
    exact sub_nonneg.mpr (hmlog.trans (mul_nonneg hcomp.constant_nonneg (by linarith)))
  refine ⟨B,hB,?_⟩
  intro n hn ε hε ε' hε'
  have hend := endpoint_difference N ha hb F hF εlo εhi K hεlo hee hεhi hcomp n hn δ hd hd16 hm
  have hscale := completionLoss_sub_log_le K hcomp.constant_nonneg n hn δ m hd
    (by linarith) hm hm1
  have hmin := exponent_mono N ha hb F hF n hn εlo ε hεlo hε.1 (hε.2.trans_lt hεhi)
  have hmax := exponent_mono N ha hb F hF n hn ε εhi (hεlo.trans_le hε.1) hε.2 hεhi
  have hmin' := exponent_mono N ha hb F hF n hn εlo ε' hεlo hε'.1 (hε'.2.trans_lt hεhi)
  have hmax' := exponent_mono N ha hb F hF n hn ε' εhi (hεlo.trans_le hε'.1) hε'.2 hεhi
  apply abs_le.mpr
  change completionLoss K n δ-Real.logb 2 m ≤ B*lossScale n at hscale
  change exponent N F εhi n-exponent N F εlo n ≤ completionLoss K n δ-Real.logb 2 m at hend
  constructor <;> linarith

/-- The literal supremum over every pair of errors in the interval. -/
def intervalDifference (N : KrausChannel a b) (F : AlternativeFamily a b)
    (εlo εhi : ℝ) (n : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ ε∈Set.Icc εlo εhi, ∃ ε'∈Set.Icc εlo εhi,
    x = |exponent N F ε n-exponent N F ε' n|}

theorem uniform_sup_bound (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (εlo εhi K : ℝ)
    (hεlo : 0<εlo) (hee : εlo≤εhi) (hεhi : εhi<1)
    (hcomp : CompletionProperty N F εlo K) :
    ∃ B : ℝ, 0≤B ∧ ∀ n : ℕ, 0<n → intervalDifference N F εlo εhi n ≤ B*lossScale n := by
  obtain ⟨B,hB,hbound⟩ := uniform_interval_bound N ha hb F hF εlo εhi K hεlo hee hεhi hcomp
  refine ⟨B,hB,?_⟩
  intro n hn
  apply csSup_le
  · exact ⟨0,εlo,⟨le_rfl,hee⟩,εlo,⟨le_rfl,hee⟩,by simp⟩
  · rintro x ⟨ε,hε,ε',hε',rfl⟩
    exact hbound n hn ε hε ε' hε'

/-- The normalized difference vanishes, proved directly from the quantitative loss. -/
theorem normalized_difference_tendsto_zero (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (εlo εhi K : ℝ)
    (hεlo : 0<εlo) (hee : εlo≤εhi) (hεhi : εhi<1)
    (hcomp : CompletionProperty N F εlo K)
    (ε ε' : ℝ) (hε : ε∈Set.Icc εlo εhi) (hε' : ε'∈Set.Icc εlo εhi) :
    Tendsto (fun n : ℕ => (exponent N F ε n-exponent N F ε' n)/(n:ℝ)) atTop (𝓝 0) := by
  obtain ⟨B,hB,hbound⟩ := uniform_interval_bound N ha hb F hF εlo εhi K hεlo hee hεhi hcomp
  have hlim : Tendsto (fun n : ℕ => B*(lossScale n/(n:ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul normalized_loss_tendsto_zero
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (show (0:ℝ)<(n:ℝ) from Nat.cast_pos.mpr hn)]
  have h := div_le_div_of_nonneg_right (hbound n hn ε hε ε' hε') (Nat.cast_nonneg n)
  simpa only [mul_div_assoc] using h

end GeneralizedChannelStein.ToleranceComparison
