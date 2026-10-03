import GeneralizedChannelStein.IterativeApproximation

/-! # Ordinary fixed-error operational limit under only F1--F3 -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter
open scoped Topology ComplexOrder
variable {a b : ℕ}

/-- Every upper testing limit is bounded by every fixed-error lower testing limit. -/
theorem limsup_le_liminf_testing (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε η : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hη1 : η < 1) :
    limsup (compositeExponent N F η) atTop ≤ lowerTestingRate N F ε := by
  by_contra! hlt
  obtain ⟨S,hbS,hSlim⟩ := EReal.exists_between_coe_real hlt
  have happrox := proposition_9 N ha hb F hF ε S hε hε1 hbS
  have hle := limsup_exponent_le_approximation_rate N F S happrox η hη1
  exact (not_lt_of_ge hle) hSlim

/-- The literal liminf is independent of every fixed tolerance in (0,1). -/
theorem lowerTestingRate_eq (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε η : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) (hη1 : η < 1) :
    lowerTestingRate N F ε = lowerTestingRate N F η := by
  apply le_antisymm
  · exact (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)).trans
      (limsup_le_liminf_testing N ha hb F hF η ε hη hη1 hε1)
  · exact (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)).trans
      (limsup_le_liminf_testing N ha hb F hF ε η hε hε1 hη1)

/-- Canonical real rate; finiteness is proved from admissibility before use. -/
def steinRate (N : KrausChannel a b) (F : AlternativeFamily a b) : ℝ :=
  (lowerTestingRate N F (1/2)).toReal

theorem lowerTestingRate_ne_top (N : KrausChannel a b) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) (ε : ℝ) (hε1 : ε < 1) :
    lowerTestingRate N F ε ≠ ⊤ := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  exact ne_of_lt ((lowerTestingRate_le_replacer N hb F hF ω hω hOne ε hε1).trans_lt
    (EReal.coe_lt_top _))

theorem steinRate_coe (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) :
    (steinRate N F : EReal) = lowerTestingRate N F (1/2) :=
  EReal.coe_toReal (lowerTestingRate_ne_top N hb F hF (1/2) (by norm_num))
    (ne_of_gt (EReal.bot_lt_zero.trans_le
      (lowerTestingRate_nonneg N ha F (1/2) (by norm_num) (by norm_num))))

theorem steinRate_nonneg (N : KrausChannel a b) (ha : 0 < a)
    (F : AlternativeFamily a b) : 0 ≤ steinRate N F :=
  EReal.toReal_nonneg (lowerTestingRate_nonneg N ha F (1/2) (by norm_num) (by norm_num))

/-- The common ordinary operational limit exists at every fixed error. -/
theorem testing_limit_extended (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (compositeExponent N F ε) atTop (𝓝 (steinRate N F : EReal)) := by
  rw [steinRate_coe N ha hb F hF, ← lowerTestingRate_eq N ha hb F hF ε (1/2)
    hε hε1 (by norm_num) (by norm_num)]
  apply tendsto_of_le_liminf_of_limsup_le le_rfl
  exact limsup_le_liminf_testing N ha hb F hF ε ε hε hε1 hε1

/-- Exponential approximation at every rate above the actual common operational rate. -/
theorem exponential_above_steinRate (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (S : ℝ) (hS : steinRate N F < S) : ExponentialFreeApprox N F S := by
  apply proposition_9 N ha hb F hF (1/2) S (by norm_num) (by norm_num)
  rw [← steinRate_coe N ha hb F hF]
  exact EReal.coe_lt_coe_iff.mpr hS

end GeneralizedChannelStein
