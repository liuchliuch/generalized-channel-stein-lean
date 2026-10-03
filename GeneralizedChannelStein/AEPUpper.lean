import GeneralizedChannelStein.Smoothing
import GeneralizedChannelStein.OperationalLimit
import QuantumChannelStein.SubchannelSmoothingRates

/-! # Upper AEP rate for the literal exact-CPTP free-family smoothing -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy Filter Asymptotics
open scoped Topology ComplexOrder
variable {a b : ℕ}

/-- The actual normalized smoothed resource cost, preserving extended values. -/
def smoothedRate (N : KrausChannel a b) (F : AlternativeFamily a b) (δ : ℕ → ℝ) (n : ℕ) : EReal :=
  (((n:ℝ)⁻¹:ℝ):EReal)*smoothedResourceMax (N.tensorPower n) (F n) (δ n)

/-- The numerical subexponential-radius estimate needs positivity only eventually. -/
theorem eventually_exponential_le_radius (δ : ℕ → ℝ)
    (hδ : ∀ᶠ n : ℕ in atTop, 0 < δ n)
    (hsub : (fun n => Real.log (1/δ n)) =o[atTop] (fun n : ℕ => (n:ℝ)))
    (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, K*Real.exp (-γ*(n:ℝ)) ≤ δ n := by
  have hg : 0 < γ/2 := by positivity
  have hsmall := hsub.bound hg
  have hlarge := eventually_nat_mul_ge (γ/2) (Real.log K) hg
  filter_upwards [hδ,hsmall,hlarge] with n hn hs hl
  have hlog : Real.log (1/δ n) ≤ γ/2*(n:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)] using
      (le_abs_self (Real.log (1/δ n))).trans hs
  rw [one_div,Real.log_inv] at hlog
  calc
    K*Real.exp (-γ*(n:ℝ)) = Real.exp (Real.log K-γ*(n:ℝ)) := by
      rw [Real.exp_sub,Real.exp_log hK,div_eq_mul_inv]
      rw [show -γ*(n:ℝ) = -(γ*(n:ℝ)) by ring,Real.exp_neg]
    _ ≤ Real.exp (Real.log (δ n)) := Real.exp_le_exp.mpr (by linarith)
    _ = δ n := Real.exp_log hn

/-- An exponentially accurate exact-TP approximation is feasible at every
subexponential positive radius. Only the scalar radius lemma is reused. -/
theorem eventually_smoothedRate_le (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 < n → 0 < δ n)
    (hsub : (fun n => Real.logb 2 (1/δ n)) =o[atTop] (fun n : ℕ => (n:ℝ)))
    (S : ℝ) (hS : steinRate N F < S) :
    ∀ᶠ n : ℕ in atTop, smoothedRate N F δ n ≤ (S:EReal) := by
  obtain ⟨K,γ,hK,hγ,happrox⟩ := exponential_above_steinRate N ha hb F hF S hS
  have hδevent : ∀ᶠ n : ℕ in atTop, 0 < δ n :=
    (eventually_gt_atTop (0:ℕ)).mono fun n hn => hδ n hn
  have hrad := eventually_exponential_le_radius δ hδevent
    (SubchannelSmoothingRates.log_inverse_isLittleO_of_base_two δ hsub) K γ hK hγ
  have hS0 : 0 ≤ S := (steinRate_nonneg N ha F).trans hS.le
  filter_upwards [happrox,hrad,eventually_gt_atTop (0:ℕ)] with n hn hr hnpos
  obtain ⟨L,M,hM,hdom,hclose⟩ := hn
  have hc : 1 ≤ (2:ℝ)^((n:ℝ)*S) := Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg n) hS0)
  have h := smoothedResourceMax_le_of_witness (N.tensorPower n) L M (F n) hM
    ((2:ℝ)^((n:ℝ)*S)) (δ n) hc hdom (hclose.trans (ENNReal.ofReal_le_ofReal hr))
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at h
  have hm := mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg n)))
  change smoothedRate N F δ n ≤ (((n:ℝ)⁻¹:ℝ):EReal)*(((n:ℝ)*S:ℝ):EReal) at hm
  rw [← EReal.coe_mul, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hnpos.ne')] at hm
  exact hm

theorem limsup_smoothedRate_le (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 < n → 0 < δ n)
    (hsub : (fun n => Real.logb 2 (1/δ n)) =o[atTop] (fun n : ℕ => (n:ℝ))) :
    limsup (smoothedRate N F δ) atTop ≤ (steinRate N F:EReal) := by
  by_contra! hlt
  obtain ⟨S,hRS,hSlim⟩ := EReal.exists_between_coe_real hlt
  have hS : steinRate N F < S := EReal.coe_lt_coe_iff.mp hRS
  have hle : limsup (smoothedRate N F δ) atTop ≤ (S:EReal) :=
    limsup_le_of_le (by isBoundedDefault) (eventually_smoothedRate_le N ha hb F hF δ hδ hsub S hS)
  exact (not_lt_of_ge hle) hSlim

end GeneralizedChannelStein
