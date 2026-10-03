import GeneralizedChannelStein.AEPUpper
import GeneralizedChannelStein.RealRates

/-! # Sharp-radius lower AEP bound for exact trace-preserving smoothing -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter Asymptotics
open scoped Topology ComplexOrder
variable {a b : ℕ}

/-- A uniform radius below two admits one fixed testing tolerance and positive margin. -/
theorem liminf_smoothedRate_ge (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) (δ : ℕ → ℝ) (δbar : ℝ)
    (hδ : ∀ n, 0 < n → 0 < δ n ∧ δ n ≤ δbar) (hbar : δbar < 2) :
    (steinRate N F:EReal) ≤ liminf (smoothedRate N F δ) atTop := by
  have hbar0 : 0 < δbar := (hδ 1 (by norm_num)).1.trans_le (hδ 1 (by norm_num)).2
  let ε := (1-δbar/2)/2
  let c := 1-ε-δbar/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hε1 : ε < 1 := by dsimp [ε]; linarith
  have hc : 0 < c := by dsimp [c,ε]; linarith
  have hi : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hreal : Tendsto (fun n : ℕ => testingRateReal N F ε n+Real.logb 2 c/(n:ℝ))
      atTop (𝓝 (steinRate N F)) := by
    simpa using (testing_limit N ha hb F hF ε hε hε1).add (hi.const_mul (Real.logb 2 c))
  have hlim : Tendsto (fun n : ℕ =>
      ((testingRateReal N F ε n+Real.logb 2 c/(n:ℝ):ℝ):EReal))
      atTop (𝓝 (steinRate N F:EReal)) := EReal.tendsto_coe.mpr hreal
  have hevent : ∀ᶠ n : ℕ in atTop,
      ((testingRateReal N F ε n+Real.logb 2 c/(n:ℝ):ℝ):EReal) ≤ smoothedRate N F δ n := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hdn := hδ n hn
    have hm : c ≤ 1-ε-δ n/2 := by dsimp [c]; linarith
    have hmpos := hc.trans_le hm
    have hf := admissible_values_finite N ha hb F hF n hn ε hε hε1
    have htest := smoothedResourceMax_testing_lower (N.tensorPower n) (pow_pos ha n)
      (F n) ε (δ n) hε.le hε1 hdn.1.le hmpos hf.2.2.1
    have hlog : Real.logb 2 c ≤ Real.logb 2 (1-ε-δ n/2) :=
      (Real.logb_le_logb (by norm_num) hc hmpos).mpr hm
    have hl : ((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal+Real.logb 2 c:ℝ):EReal) ≤
        smoothedResourceMax (N.tensorPower n) (F n) (δ n) :=
      (EReal.coe_le_coe_iff.mpr (add_le_add le_rfl hlog)).trans htest
    have hmul := mul_le_mul_of_nonneg_left hl (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg n)))
    change _ ≤ smoothedRate N F δ n at hmul
    rw [← EReal.coe_mul] at hmul
    convert hmul using 1
    congr 1
    unfold testingRateReal
    ring
  have h := liminf_le_liminf hevent (by isBoundedDefault) (by isBoundedDefault)
  rw [hlim.liminf_eq] at h
  exact h

/-- **Theorem 11**, in its genuinely extended formulation before the final
finite-value real-coordinate rewrite. Exact TP, full radius<2, subexponential errors. -/
theorem theorem_11_extended (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) (δ : ℕ → ℝ) (δbar : ℝ)
    (hδ : ∀ n, 0 < n → 0 < δ n ∧ δ n ≤ δbar) (hbar : δbar < 2)
    (hsub : (fun n => Real.logb 2 (1/δ n)) =o[atTop] (fun n : ℕ => (n:ℝ))) :
    Tendsto (smoothedRate N F δ) atTop (𝓝 (steinRate N F:EReal)) :=
  tendsto_of_le_liminf_of_limsup_le (liminf_smoothedRate_ge N ha hb F hF δ δbar hδ hbar)
    (limsup_smoothedRate_le N ha hb F hF δ (fun n hn => (hδ n hn).1) hsub)

end GeneralizedChannelStein
