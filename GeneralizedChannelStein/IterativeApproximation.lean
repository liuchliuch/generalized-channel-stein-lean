import GeneralizedChannelStein.TwoRateVanishing

/-! # Proposition 9: finite rate iteration from the literal testing liminf -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DimensionDomination FreeAmplification Filter
open scoped Topology ComplexOrder
variable {a b : ℕ}

/-- Rate enlargement preserves the same physical approximation witnesses. -/
theorem exponentialFreeApprox_mono (N : KrausChannel a b) (F : AlternativeFamily a b)
    {r s : ℝ} (hrs : r ≤ s) (h : ExponentialFreeApprox N F r) : ExponentialFreeApprox N F s := by
  obtain ⟨K,γ,hK,hγ,hevent⟩ := h
  refine ⟨K,γ,hK,hγ,?_⟩
  filter_upwards [hevent] with n hn
  obtain ⟨L,M,hM,hdom,hclose⟩ := hn
  refine ⟨L,M,hM,cpLe_scalar_mono _ M ?_ hdom,hclose⟩
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_left hrs (Nat.cast_nonneg n))

theorem replacerRate_nonneg (ω : State b) (hb : 0 < b) (hω : ω.matrix.PosDef) :
    0 ≤ replacerRate ω hb := by
  have h1 : 0 ≤ Real.logb 2 (b:ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hb)
  have h2 : Real.logb 2 (minEigenvalue ω hb) ≤ 0 :=
    (Real.logb_nonpos_iff (by norm_num) (minEigenvalue_pos ω hb hω)).mpr
      (minEigenvalue_le_one ω hb)
  unfold replacerRate
  linarith

/-- Proposition 9, with no assumed limit, rate-improvement oracle, symmetry,
or marginal closure. The rate in the premise is the actual liminf. -/
theorem proposition_9 (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε S : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hS : lowerTestingRate N F ε < (S:EReal)) : ExponentialFreeApprox N F S := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  let C := replacerRate ω hb
  have hC : 0 ≤ C := replacerRate_nonneg ω hb hω
  have hstart : ExponentialFreeApprox N F C := exponentialFreeApprox_replacer N hb F hF ω hω hOne
  obtain ⟨r₀,hbr₀,hr₀S⟩ := EReal.exists_between_coe_real hS
  have hr₀S' : r₀ < S := EReal.coe_lt_coe_iff.mp hr₀S
  have hr₀pos : 0 < r₀ := by
    have h := (lowerTestingRate_nonneg N ha F ε hε.le hε1.le).trans_lt hbr₀
    exact EReal.coe_lt_coe_iff.mp h
  let r := (r₀+S)/2
  have hr₀r : r₀ < r := by dsimp [r]; linarith
  have hrS : r < S := by dsimp [r]; linarith
  have hr : 0 ≤ r := by linarith
  by_cases hCr : C ≤ r
  · exact exponentialFreeApprox_mono N F (hCr.trans hrS.le) hstart
  have hrC : r < C := lt_of_not_ge hCr
  let d := Real.sqrt (1-ε)
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hd1 : d < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr
    linarith
  obtain ⟨η,z,κ,hη,hη1,hz,hκ,_,htail⟩ := TwoRateScalars.exists_two_rate_tail_parameters hd hd1
  have hstep : ∀ s s' : ℝ, r < s → (1-η)*r+η*s < s' →
      ExponentialFreeApprox N F s → ExponentialFreeApprox N F s' := by
    intro s s' hrs hgap hs
    let S' := s+(s'-((1-η)*r+η*s))/(2*η)
    have hsS : s < S' := by
      dsimp [S']
      have hpos := div_pos (sub_pos.mpr hgap) (by positivity : (0:ℝ)<2*η)
      linarith
    have hnew : r+η*(S'-r) < s' := by
      have heq : r+η*(S'-r) = (((1-η)*r+η*s)+s')/2 := by
        dsimp [S']
        field_simp
        ring
      rw [heq]
      linarith
    have hv := two_rate_vanishing N ha hb F hF ε r₀ r s S' η z κ hε hε1 hbr₀ hr₀r
      hr hrs hsS hη.le hz.le hκ htail hs
    apply exponential_of_vanishing N F ha hF.convex hF.tensor_closed ω
      (replacer_power_mem F hF.tensor_closed ω hOne) C hC
      (faithful_replacer_domination N ω hb hω) (r+η*(S'-r)) s'
      (add_nonneg hr (mul_nonneg hη.le (by linarith))) hnew hv
  obtain ⟨j,hj,hP⟩ := TwoRateScalars.exists_improved_rate hrC hrS hη hη1 hstart hstep
  exact exponentialFreeApprox_mono N F hj.le hP

end GeneralizedChannelStein
