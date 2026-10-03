import GeneralizedChannelStein.TwoRateCompletion
import GeneralizedChannelStein.TwoRateNumerics

/-! # Proposition 9's actual square-block improvement step

The free dominator is selected anew at each good block. All analytical scalar
conditions are discharged below; the output is a literal family of normalized
approximants with vanishing error at arbitrarily late square blocklengths.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy TestingPrimal UniformAuxiliary
  FreeAmplification Filter
open scoped Topology ComplexOrder MatrixOrder
variable {a b : ℕ}

/-- A fixed Chernoff fraction gives a true improvement of the higher free rate. -/
theorem two_rate_vanishing (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ε r₀ r s S η z κ : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hr₀ : lowerTestingRate N F ε < (r₀:EReal)) (hr₀r : r₀ < r)
    (hr : 0 ≤ r) (hrs : r < s) (hsS : s < S)
    (hη : 0 ≤ η) (hz : 1 ≤ z) (hκ : 0 < κ)
    (htail : ∀ m : ℕ,
      z^(-(η*m))*(1+Real.sqrt (1-ε)+z*((1+Real.sqrt (1-ε))/2))^m =
        Real.exp (-κ*(m:ℝ)))
    (hexp : ExponentialFreeApprox N F s) :
    VanishingFreeApprox N F (r+η*(S-r)) := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  obtain ⟨K,γ,hK,hγ,happrox⟩ := hexp
  let d := Real.sqrt (1-ε)
  let q := r+η*(S-r)
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hd1 : d < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr
    linarith
  have hd2 : d^2 = 1-ε := Real.sq_sqrt (by linarith)
  have hq : 0 ≤ q := add_nonneg hr (mul_nonneg hη (by linarith))
  intro R hqR δ hδ k₀
  have herrsmall : ∀ᶠ n : ℕ in atTop,
      Real.exp (-κ*(n:ℝ))+(n:ℝ)*strongBlockError K γ n*
        Real.exp ((n:ℝ)*strongBlockError K γ n) ≤ δ/8 :=
    (square_block_error_tendsto K γ κ hγ hκ).eventually_le_const (by positivity)
  have hesmall : ∀ᶠ n : ℕ in atTop, strongBlockError K γ n ≤ (1-d)/2 :=
    (strongBlockError_tendsto K γ hγ).eventually_le_const (by linarith)
  have hgood : ∃ᶠ n : ℕ in atTop, compositeExponent N F ε n < (r₀:EReal) :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hr₀
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 < n ∧ k₀ ≤ n ∧ FreeApproxAt N F n s (K*Real.exp (-γ*(n:ℝ))) ∧
      strongBlockError K γ n ≤ (1-d)/2 ∧
      Real.exp (-κ*(n:ℝ))+(n:ℝ)*strongBlockError K γ n*
        Real.exp ((n:ℝ)*strongBlockError K γ n) ≤ δ/8 ∧
      1 ≤ (n:ℝ)*(r-r₀) ∧ 1 ≤ (n:ℝ)*(S-s) ∧ 5 ≤ (n:ℝ)*(R-q) := by
    filter_upwards [eventually_gt_atTop (0:ℕ),eventually_ge_atTop k₀,happrox,hesmall,herrsmall,
      eventually_nat_mul_ge (r-r₀) 1 (sub_pos.mpr hr₀r),
      eventually_nat_mul_ge (S-s) 1 (sub_pos.mpr hsS),
      eventually_nat_mul_ge (R-q) 5 (sub_pos.mpr hqR)] with n h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  obtain ⟨n,hgoodn,hn,hkn,happroxn,hen,hu,hra,hrb,hrc⟩ := (hgood.and_eventually hevent).exists
  obtain ⟨L,T,hT,hLT,hclose⟩ := happroxn
  have hvals := admissible_values_finite N ha hb F hF n hn ε hε hε1
  let β := (compositeBeta (N.tensorPower n) (F n) ε).toReal
  have hβ : 0 < β := ENNReal.toReal_pos hvals.2.2.1.ne' hvals.2.2.2.ne
  have hβlow : (2:ℝ)^(-(n:ℝ)*r₀) < β :=
    beta_lower_of_exponent_lt n hn _ hvals.2.2.1 hvals.2.2.2.ne r₀ hgoodn
  obtain ⟨M,hM,hrough⟩ := exists_rough_free_alternative (N.tensorPower n) (pow_pos ha n)
    (F n) (hF.channels n hn) (hF.compact n hn) (hF.convex n hn) (hF.nonempty n hn)
    ε hε.le hε1 hvals.2.2.1
  let e := strongBlockError K γ n
  let c := (2:ℝ)^((n:ℝ)*n*q+4*n)
  have he : 0 ≤ e := strongBlockError_nonneg _ _ _
  have hcostA : Real.sqrt (2*(ε/β)) ≤ (2:ℝ)^((n:ℝ)*r/2) :=
    rough_cost_bound n ε β r₀ r hε1.le hβ hβlow.le hra
  have hcostB : Real.sqrt (2*(2:ℝ)^((n:ℝ)*s)) ≤ (2:ℝ)^((n:ℝ)*S/2) :=
    strong_cost_bound n s S hrb
  have hclose' : DiamondNorm.diamondNorm (L.toLinearMap-(N.tensorPower n).toLinearMap) ≤
      ENNReal.ofReal (2*e^2) := by
    apply hclose.trans (ENNReal.ofReal_le_ofReal ?_)
    have he2 := strongBlockError_sq K γ hK.le n
    change e^2 = _ at he2
    nlinarith [sq_nonneg e]
  have hc : 1 ≤ c := Real.one_le_rpow (by norm_num) (by positivity)
  obtain ⟨L',U,hU,hLU,herr⟩ := two_rate_completed_block N ha F hF ω hOne n n hn hn M T L
    hM hT (ε/β) ((2:ℝ)^((n:ℝ)*s)) d e r S η z c (by positivity) (by positivity) hd he
    (by rw [hd2]; exact hrough) hLT hclose' hen (by linarith) hz hcostA hcostB hc
    (square_cost_bound n q)
  refine ⟨n*n,le_trans hkn (by nlinarith),Nat.mul_pos hn hn,L',U,hU,?_,?_⟩
  · apply cpLe_scalar_mono L'.toLinearMap U _ hLU
    simpa only [Nat.cast_mul] using square_cost_add_one_le n hn q R hq hrc
  · apply herr.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [htail]
    have htel := telescoping_error_envelope n e he
    change Real.exp (-κ*(n:ℝ))+(n:ℝ)*e*Real.exp ((n:ℝ)*e) ≤ δ/8 at hu
    nlinarith

end GeneralizedChannelStein
