import GeneralizedChannelStein.QuantitativeCompletion
import GeneralizedChannelStein.ToleranceComparison
import GeneralizedChannelStein.CompletionComponents

/-! # Corollary 17 and Lemma 18, with the actual completion theorem discharged -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter
open scoped Topology
variable {a b : ℕ}

/-- Corollary 17: a single finite nonnegative constant covers all blocks and permitted radii. -/
theorem corollary_17 (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 0<n → ∀ δ : ℝ, 0<δ → δ≤1/16 → ε+δ/2<1 →
      (((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
        Real.logb 2 (1-ε-δ/2) : ℝ) : EReal) ≤ smoothedResourceMax (N.tensorPower n) (F n) δ) ∧
      (smoothedResourceMax (N.tensorPower n) (F n) δ ≤
        ((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
          completionLoss K n δ : ℝ) : EReal)) := by
  obtain ⟨K,hK⟩ := theorem_16_exists N ha hb F hF hQ ε hε hε1
  exact ⟨K,hK.constant_nonneg,CompletionConsequences.smoothing_bounds N ha hb F hF ε K hε hε1 hK⟩

/-- Corollary 17's lower half holds under F1–F3 alone at every valid full diamond radius. -/
theorem corollary_17_lower (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) (n : ℕ) (hn : 0<n)
    (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ<2*(1-ε)) :
    ((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
      Real.logb 2 (1-ε-δ/2) : ℝ) : EReal) ≤ smoothedResourceMax (N.tensorPower n) (F n) δ :=
  CompletionConsequences.smoothing_lower N ha hb F hF ε hε hε1 n hn δ hδ (by linarith)

/-- Lemma 18: the literal supremum over the entire closed error interval. -/
theorem lemma_18 (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F)
    (εlo εhi : ℝ) (hlo : 0<εlo) (hle : εlo≤εhi) (hhi : εhi<1) :
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 0<n →
      ToleranceComparison.intervalDifference N F εlo εhi n ≤
        K*((n:ℝ)^((2:ℝ)/3)*Real.logb 2 ((n:ℝ)+1)) := by
  obtain ⟨K,hK⟩ := theorem_16_exists N ha hb F hF hQ εlo hlo (hle.trans_lt hhi)
  exact ToleranceComparison.uniform_sup_bound N ha hb F hF εlo εhi K hlo hle hhi hK

/-- The pointwise uniform form makes the interval's two universal error quantifiers explicit. -/
theorem lemma_18_uniform (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F)
    (εlo εhi : ℝ) (hlo : 0<εlo) (hle : εlo≤εhi) (hhi : εhi<1) :
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 0<n → ∀ ε∈Set.Icc εlo εhi, ∀ ε'∈Set.Icc εlo εhi,
      |ToleranceComparison.exponent N F ε n-ToleranceComparison.exponent N F ε' n| ≤
        K*((n:ℝ)^((2:ℝ)/3)*Real.logb 2 ((n:ℝ)+1)) := by
  obtain ⟨K,hK⟩ := theorem_16_exists N ha hb F hF hQ εlo hlo (hle.trans_lt hhi)
  exact ToleranceComparison.uniform_interval_bound N ha hb F hF εlo εhi K hlo hle hhi hK

/-- Every two fixed tolerances have vanishing normalized difference by the finite bound itself. -/
theorem lemma_18_normalized (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F)
    (ε ε' : ℝ) (hε : 0<ε) (hε1 : ε<1) (hε' : 0<ε') (hε'1 : ε'<1) :
    Tendsto (fun n : ℕ =>
      (ToleranceComparison.exponent N F ε n-ToleranceComparison.exponent N F ε' n)/(n:ℝ))
      atTop (𝓝 0) := by
  have hlo : 0<min ε ε' := lt_min hε hε'
  have hhi : max ε ε'<1 := max_lt hε1 hε'1
  have hle : min ε ε'≤max ε ε' := (min_le_left _ _).trans (le_max_left _ _)
  obtain ⟨K,hK⟩ := theorem_16_exists N ha hb F hF hQ (min ε ε') hlo (hle.trans_lt hhi)
  exact ToleranceComparison.normalized_difference_tendsto_zero N ha hb F hF
    (min ε ε') (max ε ε') K hlo hle hhi hK ε ε'
    ⟨min_le_left _ _,le_max_left _ _⟩ ⟨min_le_right _ _,le_max_right _ _⟩

end GeneralizedChannelStein
