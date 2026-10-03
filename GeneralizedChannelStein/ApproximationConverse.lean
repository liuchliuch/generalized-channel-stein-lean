import GeneralizedChannelStein.FreeApproximation
import GeneralizedChannelStein.ApproximationTesting
import QuantumChannelStein.ParallelExponent

/-! # Uniform testing converse from a constructed free approximation

These composition lemmas retain their explicit approximation premise. They do
not claim the main theorem before Proposition 9 constructs that premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy OperationalTesting ParallelExponent Filter
open scoped Topology
variable {a b : ℕ}

/-- A constructed free approximation at S gives an exponential uniform converse
at every r>S, for arbitrary mixed inputs and arbitrary finite references. -/
theorem exponential_converse_of_approximation (N : KrausChannel a b)
    (F : AlternativeFamily a b) (S r : ℝ) (hSr : S < r)
    (happrox : ExponentialFreeApprox N F S) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ t : ChannelTest (a^n) (b^n),
        worstAcceptance (F n) t ≤ ENNReal.ofReal ((2:ℝ)^(-(n:ℝ)*r)) →
        t.acceptance (N.tensorPower n) ≤ K*Real.exp (-γ*(n:ℝ)) := by
  obtain ⟨K,γ,hK,hγ,hevent⟩ := happrox
  refine ⟨1+K/2,min ((r-S)*Real.log 2) γ,by positivity,
    lt_min (mul_pos (sub_pos.mpr hSr) (Real.log_pos (by norm_num))) hγ,?_⟩
  filter_upwards [hevent] with n hn
  obtain ⟨L,M,hM,hdom,hclose⟩ := hn
  intro t hq
  have hqM : t.acceptance M ≤ (2:ℝ)^(-(n:ℝ)*r) := by
    have h := (acceptance_le_worst (F n) t M hM).trans hq
    exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg (by norm_num) _)).mp h
  have h := test_acceptance_le_approximation (N.tensorPower n) L M
    ((2:ℝ)^((n:ℝ)*S)) (K*Real.exp (-γ*(n:ℝ))) (by positivity) hdom hclose t
  have hprod : (2:ℝ)^((n:ℝ)*S) * (2:ℝ)^(-(n:ℝ)*r) =
      Real.exp (-((r-S)*Real.log 2)*(n:ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_left hqM
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ((n:ℝ)*S))
  rw [hprod] at hmul
  have hp : t.acceptance (N.tensorPower n) ≤
      Real.exp (-((r-S)*Real.log 2)*(n:ℝ)) + (K/2)*Real.exp (-γ*(n:ℝ)) := by linarith
  exact hp.trans (ScalarBounds.exp_sum_le (Nat.cast_nonneg n) (by positivity))

/-- The converse forces every fixed-error optimized beta above each strict rate. -/
theorem eventually_beta_lower_of_approximation (N : KrausChannel a b)
    (F : AlternativeFamily a b) (S r : ℝ) (hSr : S < r)
    (happrox : ExponentialFreeApprox N F S) (ε : ℝ) (hε : ε < 1) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ((2:ℝ)^(-(n:ℝ)*r)) ≤ compositeBeta (N.tensorPower n) (F n) ε := by
  obtain ⟨K,γ,hK,hγ,hevent⟩ := exponential_converse_of_approximation N F S r hSr happrox
  have hlim : Tendsto (fun n : ℕ => K*Real.exp (-γ*(n:ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      TwoRateScalars.stretched_error_tendsto_zero K hγ (by norm_num : (0:ℝ)<1)
  have hsmall := hlim.eventually (gt_mem_nhds (by linarith : (0:ℝ)<1-ε))
  filter_upwards [hevent,hsmall] with n hn hs
  apply le_iInf
  intro t
  by_contra! hq
  have hp := hn t.val hq.le
  linarith [t.property]

/-- Actual extended composite exponent, finite under admissibility at positive blocks. -/
def compositeExponent (N : KrausChannel a b) (F : AlternativeFamily a b)
    (ε : ℝ) (n : ℕ) : EReal := testingExponent n (compositeBeta (N.tensorPower n) (F n) ε)

theorem limsup_exponent_le_approximation_rate (N : KrausChannel a b)
    (F : AlternativeFamily a b) (S : ℝ) (happrox : ExponentialFreeApprox N F S)
    (ε : ℝ) (hε : ε < 1) :
    limsup (compositeExponent N F ε) atTop ≤ (S:EReal) := by
  by_contra! hlt
  obtain ⟨r,hSr,hrlim⟩ := EReal.exists_between_coe_real hlt
  have hSr' : S < r := EReal.coe_lt_coe_iff.mp hSr
  have hevent : ∀ᶠ n : ℕ in atTop, compositeExponent N F ε n ≤ (r:EReal) := by
    filter_upwards [eventually_beta_lower_of_approximation N F S r hSr' happrox ε hε,
      eventually_gt_atTop (0:ℕ)] with n hn hnpos
    exact (testingExponent_antitone n hn).trans_eq (testingExponent_two_rpow n hnpos r)
  have hle : limsup (compositeExponent N F ε) atTop ≤ (r:EReal) :=
    limsup_le_of_le (by isBoundedDefault) hevent
  exact (not_lt_of_ge hle) hrlim

end GeneralizedChannelStein
