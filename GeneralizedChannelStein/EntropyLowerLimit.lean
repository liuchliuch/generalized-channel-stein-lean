import GeneralizedChannelStein.RealRates

/-! # The weak converse gives the entropy-rate lower limit -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter
open scoped Topology ComplexOrder
variable {a b : ℕ}

theorem entropyRateReal_boundedAbove (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) :
    atTop.IsBoundedUnder (· ≤ ·) (entropyRateReal N F) := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  refine ⟨replacerRate ω hb, ?_⟩
  change ∀ᶠ n : ℕ in atTop, entropyRateReal N F n ≤ replacerRate ω hb
  exact Eventually.of_forall fun n => (entropyRateReal_bounds N ha hb F hF ω hω hOne n).2

theorem entropyRateReal_boundedBelow (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) :
    atTop.IsBoundedUnder (· ≥ ·) (entropyRateReal N F) := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  refine ⟨0, ?_⟩
  change ∀ᶠ n : ℕ in atTop, 0 ≤ entropyRateReal N F n
  exact Eventually.of_forall fun n => (entropyRateReal_bounds N ha hb F hF ω hω hOne n).1

/-- Fixed tolerance is taken before the limit, exactly as in the paper. -/
theorem entropy_liminf_ge_fixed_error (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (1-ε)*steinRate N F ≤ liminf (entropyRateReal N F) atTop := by
  have hlim : Tendsto (fun n : ℕ => (1-ε)*testingRateReal N F ε n-1/(n:ℝ)) atTop
      (𝓝 ((1-ε)*steinRate N F)) := by
    simpa only [sub_zero] using
      ((testing_limit N ha hb F hF ε hε hε1).const_mul (1-ε)).sub
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hevent : ∀ᶠ n : ℕ in atTop,
      (1-ε)*testingRateReal N F ε n-1/(n:ℝ) ≤ entropyRateReal N F n := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact normalized_weak_converse N ha hb F hF ε hε hε1 n hn
  have h := liminf_le_liminf hevent hlim.isBoundedUnder_ge
    (entropyRateReal_boundedAbove N ha hb F hF).isCobounded_flip
  rw [hlim.liminf_eq] at h
  exact h

/-- Only after the block limit is bounded do the tolerances tend to zero. -/
theorem entropy_liminf_ge_steinRate (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) :
    steinRate N F ≤ liminf (entropyRateReal N F) atTop := by
  let ε : ℕ → ℝ := fun j => 1/((j:ℝ)+2)
  have hε0 (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε1 (j : ℕ) : ε j < 1 := by
    dsimp [ε]
    apply (div_lt_one (by positivity : (0:ℝ)<(j:ℝ)+2)).mpr
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have he : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [ε,Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h
  have hlim : Tendsto (fun j : ℕ => (1-ε j)*steinRate N F) atTop (𝓝 (steinRate N F)) := by
    simpa only [sub_zero,one_mul] using ((tendsto_const_nhds (x := (1:ℝ))).sub he).mul_const (steinRate N F)
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun j => entropy_liminf_ge_fixed_error N ha hb F hF (ε j) (hε0 j) (hε1 j)

end GeneralizedChannelStein
