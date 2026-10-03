import GeneralizedChannelStein.EntropyLowerLimit
import GeneralizedChannelStein.EntropyComparison

/-! # Identification of the ordinary optimized Umegaki entropy limit -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy EntropyComparison EntropyContinuity Filter
open scoped Topology ComplexOrder
variable {a b : ℕ}

/-- Every rate above the already proved operational limit bounds the entropy limsup. -/
theorem entropy_limsup_le_strict_rate (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (S : ℝ) (hS : steinRate N F < S) : limsup (entropyRateReal N F) atTop ≤ S := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  obtain ⟨K,γ,hK,hγ,happrox⟩ := exponential_above_steinRate N ha hb F hF S hS
  let δ : ℕ → ℝ := fun n => K*Real.exp (-γ*(n:ℝ))
  let D := replacerRate ω hb+Real.logb 2 ((a:ℝ)*b)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ,Real.rpow_one] using
      TwoRateScalars.stretched_error_tendsto_zero K hγ (by norm_num : (0:ℝ)<1)
  have hi : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hup : Tendsto (fun n : ℕ => S+2/(n:ℝ)+(δ n/2)*(D+1/(n:ℝ))) atTop (𝓝 S) := by
    have h2 : Tendsto (fun n : ℕ => 2/(n:ℝ)) atTop (𝓝 0) := by
      simpa using hi.const_mul 2
    have hd := (hδ.div_const 2).mul ((tendsto_const_nhds (x := D)).add hi)
    simpa using ((tendsto_const_nhds (x := S)).add h2).add hd
  have hevent : ∀ᶠ n : ℕ in atTop,
      entropyRateReal N F n ≤ S+2/(n:ℝ)+(δ n/2)*(D+1/(n:ℝ)) := by
    filter_upwards [happrox,hδ.eventually_le_const (by norm_num : (0:ℝ)<1),
      eventually_gt_atTop (0:ℕ)] with n hn hδ1 hnpos
    obtain ⟨L,M,hM,hdom,hclose⟩ := hn
    have hbnd := lemma_10_of_admissible N hb F hF ω hω hOne n hnpos L M hM
      ((n:ℝ)*S) (δ n) (by dsimp [δ]; positivity) hδ1 hdom hclose
    have hf := admissible_values_finite N ha hb F hF n hnpos (1/2) (by norm_num) (by norm_num)
    rw [← EReal.coe_toReal hf.1 hf.2.1] at hbnd
    have hr := EReal.coe_le_coe_iff.mp hbnd
    have hr' : (familyEntropy (N.tensorPower n) (F n)).toReal ≤
        (n:ℝ)*S+2+(δ n/2)*((n:ℝ)*D+1) := by
      have hent := binaryEntropy_le_one (δ n/2)
      dsimp [D]
      norm_cast at hr ⊢
      linarith
    have hn0 : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr hnpos).ne'
    calc
      entropyRateReal N F n ≤ ((n:ℝ)*S+2+(δ n/2)*((n:ℝ)*D+1))/(n:ℝ) :=
        div_le_div_of_nonneg_right hr' (Nat.cast_nonneg n)
      _ = _ := by field_simp
  have hlim := limsup_le_limsup hevent
    (entropyRateReal_boundedBelow N ha hb F hF).isCobounded_flip hup.isBoundedUnder_le
  rw [hup.limsup_eq] at hlim
  exact hlim

theorem entropy_limsup_le_steinRate (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) :
    limsup (entropyRateReal N F) atTop ≤ steinRate N F := by
  by_contra! hlt
  let S := (steinRate N F+limsup (entropyRateReal N F) atTop)/2
  have hS : steinRate N F < S := by dsimp [S]; linarith
  have h := entropy_limsup_le_strict_rate N ha hb F hF S hS
  dsimp [S] at h
  linarith

/-- The ordinary entropy limit is identified with the same operational rate. -/
theorem entropy_limit (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) :
    Tendsto (entropyRateReal N F) atTop (𝓝 (steinRate N F)) :=
  tendsto_of_le_liminf_of_limsup_le (entropy_liminf_ge_steinRate N ha hb F hF)
    (entropy_limsup_le_steinRate N ha hb F hF)
    (entropyRateReal_boundedAbove N ha hb F hF) (entropyRateReal_boundedBelow N ha hb F hF)

end GeneralizedChannelStein
