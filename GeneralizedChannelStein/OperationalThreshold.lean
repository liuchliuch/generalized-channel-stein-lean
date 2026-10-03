import GeneralizedChannelStein.RealRates
import QuantumChannelStein.BelowThresholdTestFamilies

/-! # Theorem 12: one achievable uniform tester sequence and all-block strong converse -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy OperationalTesting Filter
open scoped Topology
variable {a b : ℕ}

/-- One sequence of actual uniform testers achieves target acceptance one and the exact rate. -/
theorem exists_uniform_testers (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) :
    ∃ t : (n : ℕ) → ChannelTest (a^n) (b^n),
      Tendsto (fun n => (t n).acceptance (N.tensorPower n)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => -Real.logb 2 (worstAcceptance (F n) (t n)).toReal/(n:ℝ))
        atTop (𝓝 (steinRate N F)) := by
  classical
  let ε : ℕ → ℝ := fun j => 1/((j:ℝ)+2)
  have hε0 (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε1 (j : ℕ) : ε j < 1 := by
    dsimp [ε]
    apply (div_lt_one (by positivity : (0:ℝ)<(j:ℝ)+2)).mpr
    have h : (0:ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have he : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [ε,Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h
  have hop : ∀ j n : ℕ, ∃ t : ChannelTest (a^n) (b^n),
      1-ε j ≤ t.acceptance (N.tensorPower n) ∧
      worstAcceptance (F n) t = compositeBeta (N.tensorPower n) (F n) (ε j) := by
    intro j n
    obtain ⟨ψ,T,hp,hq⟩ := lemma_5_optimal_tester (N.tensorPower n) (pow_pos ha n) (F n) (ε j) (hε0 j).le
    refine ⟨ofPureTest ψ T,?_,?_⟩
    · simpa only [ofPureTest_acceptance] using hp
    · simpa only [worstAcceptance,ofPureTest_acceptance] using hq.symm
  choose test htest using hop
  have hM (j : ℕ) : ∃ M : ℕ, ∀ n ≥ M,
      |testingRateReal N F (ε j) n-steinRate N F| ≤ ε j := by
    have hlim := testing_limit N ha hb F hF (ε j) (hε0 j) (hε1 j)
    have hev := hlim.eventually (Metric.ball_mem_nhds _ (hε0 j))
    apply eventually_atTop.mp
    exact hev.mono fun n hn => (by simpa only [Metric.mem_ball,Real.dist_eq] using hn.le)
  choose M hM using hM
  let d : ℕ → ℕ := fun n => Nat.findGreatest (fun j => M j ≤ n) n
  have hd : Tendsto d atTop atTop := by
    apply tendsto_atTop.2
    intro j
    filter_upwards [eventually_ge_atTop (max j (M j))] with n hn
    exact Nat.le_findGreatest ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  let t := fun n => test (d n) n
  have herr : ∀ᶠ n : ℕ in atTop,
      |(-Real.logb 2 (worstAcceptance (F n) (t n)).toReal/(n:ℝ))-steinRate N F| ≤ ε (d n) := by
    filter_upwards [eventually_ge_atTop (M 0)] with n hn
    have hh : M (d n) ≤ n := Nat.findGreatest_spec (P := fun j => M j ≤ n) (Nat.zero_le n) hn
    rw [(htest (d n) n).2]
    exact hM (d n) n hh
  refine ⟨t,?_,?_⟩
  · have hlo : Tendsto (fun n => 1-ε (d n)) atTop (𝓝 (1:ℝ)) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (he.comp hd)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
      (Eventually.of_forall fun n => (htest (d n) n).1)
      (Eventually.of_forall fun n => (t n).acceptance_le_one _)
  · have hlo : Tendsto (fun n => steinRate N F-ε (d n)) atTop (𝓝 (steinRate N F)) := by
      simpa using (tendsto_const_nhds (x := steinRate N F)).sub (he.comp hd)
    have hhi : Tendsto (fun n => steinRate N F+ε (d n)) atTop (𝓝 (steinRate N F)) := by
      simpa using (tendsto_const_nhds (x := steinRate N F)).add (he.comp hd)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
      (herr.mono fun n hn => by have := (abs_le.mp hn).1; linarith)
      (herr.mono fun n hn => by have := (abs_le.mp hn).2; linarith)

/-- The finite prefix is absorbed into one positive constant; this is all n. -/
theorem strong_converse_all (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (r : ℝ) (hr : steinRate N F < r) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ n : ℕ, ∀ t : ChannelTest (a^n) (b^n),
      worstAcceptance (F n) t ≤ ENNReal.ofReal ((2:ℝ)^(-(n:ℝ)*r)) →
      t.acceptance (N.tensorPower n) ≤ K*(2:ℝ)^(-c*(n:ℝ)) := by
  let S := (steinRate N F+r)/2
  have hRS : steinRate N F < S := by dsimp [S]; linarith
  have hSr : S < r := by dsimp [S]; linarith
  obtain ⟨K,γ,hK,hγ,hev⟩ := exponential_converse_of_approximation N F S r hSr
    (exponential_above_steinRate N ha hb F hF S hRS)
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hev
  let K' := K+Real.exp (γ*(n₀:ℝ))
  let c := γ/Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := div_pos hγ hlog
  have heq (n : ℕ) : (2:ℝ)^(-c*(n:ℝ)) = Real.exp (-γ*(n:ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1
    dsimp [c]
    field_simp
  refine ⟨K',c,by dsimp [K']; positivity,hc,?_⟩
  intro n t hq
  rw [heq]
  by_cases hn : n₀ ≤ n
  · exact (hn₀ n hn t hq).trans (mul_le_mul_of_nonneg_right
      (by dsimp [K']; have := Real.exp_pos (γ*(n₀:ℝ)); linarith) (Real.exp_pos _).le)
  · have hnn : (n:ℝ) ≤ n₀ := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hn))
    have hprod : 1 ≤ Real.exp (γ*(n₀:ℝ))*Real.exp (-γ*(n:ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith
    exact (t.acceptance_le_one _).trans (hprod.trans (mul_le_mul_of_nonneg_right
      (by dsimp [K']; linarith) (Real.exp_pos _).le))

/-- **Theorem 12**, both operational conclusions with the same canonical rate. -/
theorem theorem_12 (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) :
    (∃ t : (n : ℕ) → ChannelTest (a^n) (b^n),
      Tendsto (fun n => (t n).acceptance (N.tensorPower n)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => -Real.logb 2 (worstAcceptance (F n) (t n)).toReal/(n:ℝ))
        atTop (𝓝 (steinRate N F))) ∧
    (∀ r : ℝ, steinRate N F < r → ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ n : ℕ, ∀ t : ChannelTest (a^n) (b^n),
      worstAcceptance (F n) t ≤ ENNReal.ofReal ((2:ℝ)^(-(n:ℝ)*r)) →
      t.acceptance (N.tensorPower n) ≤ K*(2:ℝ)^(-c*(n:ℝ))) :=
  ⟨exists_uniform_testers N ha hb F hF,strong_converse_all N ha hb F hF⟩

end GeneralizedChannelStein
