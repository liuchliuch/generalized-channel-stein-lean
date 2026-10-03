import QuantumChannelStein.MaxRelativeEntropy
import QuantumChannelStein.DominatedSubchannelFamilies

/-! # Upper asymptotic rates for actual diamond-smoothed subchannel Dmax -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SubchannelSmoothingRates
open MaxRelativeEntropy DominatedSubchannelFamilies ChannelEntropy Filter Asymptotics
open scoped Topology
variable {a b : ℕ}

/-- Actual per-use smoothed max-relative entropy, in extended reals. -/
def smoothingRate (Φ Ψ : KrausChannel a b) (ε : ℕ → ℝ) (k : ℕ) : EReal :=
  (((k : ℝ)⁻¹ : ℝ) : EReal) * smoothedMaxRelativeEntropy (Φ.tensorPower k) (Ψ.tensorPower k) (ε k)

/-- Any subexponential positive radius eventually dominates every strictly
decaying exponential. This is a numerical theorem, not a feasibility premise. -/
theorem eventually_exponential_le_radius (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hsub : (fun k : ℕ => Real.log (1 / ε k)) =o[atTop] (fun k : ℕ => (k : ℝ)))
    (K γ : ℝ) (hK : 0 < K) (hγ : 0 < γ) :
    ∀ᶠ k : ℕ in atTop, K * Real.exp (-γ * k) ≤ ε k := by
  have hhalf : 0 < γ / 2 := by positivity
  have hsmall := hsub.bound hhalf
  have hlarge : ∀ᶠ k : ℕ in atTop, Real.log K / (γ / 2) ≤ (k : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hsmall, hlarge] with k hk hn
  have hlog : Real.log (1 / ε k) ≤ γ / 2 * (k : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)] using
      (le_abs_self (Real.log (1 / ε k))).trans hk
  have hKlog : Real.log K ≤ (k : ℝ) * (γ / 2) := (div_le_iff₀ hhalf).mp hn
  rw [one_div, Real.log_inv] at hlog
  calc
    K * Real.exp (-γ * k) = Real.exp (Real.log K - γ * k) := by
      rw [show -γ * (k : ℝ) = -(γ * k) by ring, Real.exp_neg,
        Real.exp_sub, Real.exp_log hK, div_eq_mul_inv]
    _ ≤ Real.exp (Real.log (ε k)) := Real.exp_le_exp.mpr (by linarith)
    _ = ε k := Real.exp_log (hε k)

/-- Exact conversion of the paper's base-two little-o condition to natural logs. -/
theorem log_inverse_isLittleO_of_base_two (ε : ℕ → ℝ)
    (hsub : (fun k : ℕ => Real.log (1 / ε k) / Real.log 2) =o[atTop]
      (fun k : ℕ => (k : ℝ))) :
    (fun k : ℕ => Real.log (1 / ε k)) =o[atTop] (fun k : ℕ => (k : ℝ)) := by
  have h := hsub.const_mul_left (Real.log 2)
  convert h using 1
  ext k
  field_simp

/-- The actual Corollary 5.2 family is eventually feasible at every radius
which dominates all exponentially decaying errors. -/
theorem eventually_smoothingRate_le (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (ε : ℕ → ℝ)
    (hradius : ∀ K γ : ℝ, 0 < K → 0 < γ →
      ∀ᶠ k : ℕ in atTop, K * Real.exp (-γ * k) ≤ ε k)
    (S : ℝ) (hS : (regularizedD Φ Ψ).toReal < S) :
    ∀ᶠ k : ℕ in atTop, smoothingRate Φ Ψ ε k ≤ (S : EReal) := by
  obtain ⟨K, γ, hK, hγ, L, N, hL⟩ := corollary_5_2 Φ Ψ ha hfinite S hS
  filter_upwards [eventually_ge_atTop N, eventually_gt_atTop (0 : ℕ), hradius K γ hK hγ]
    with k hk hkpos hεk
  have hLk := hL k hk
  have hD := (smoothedMaxRelativeEntropy_le (Φ.tensorPower k) (Ψ.tensorPower k) (ε k)
    (L k) (hLk.2.trans (ENNReal.ofReal_le_ofReal hεk))).trans
      (maxRelativeEntropy_le_of_two_rpow (L k).toLinearMap (Ψ.tensorPower k)
        ((k : ℝ) * S) hLk.1)
  have hm := mul_le_mul_of_nonneg_left hD
    (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg k)))
  change smoothingRate Φ Ψ ε k ≤ (((k : ℝ)⁻¹ : ℝ) : EReal) * (((k : ℝ) * S : ℝ) : EReal) at hm
  rw [← EReal.coe_mul, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hkpos.ne')] at hm
  exact hm

/-- Every strict upper rate bounds the limsup of the actual smoothed exponent. -/
theorem limsup_smoothingRate_le (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (ε : ℕ → ℝ)
    (hradius : ∀ K γ : ℝ, 0 < K → 0 < γ →
      ∀ᶠ k : ℕ in atTop, K * Real.exp (-γ * k) ≤ ε k) :
    limsup (smoothingRate Φ Ψ ε) atTop ≤ regularizedD Φ Ψ := by
  have hbot : regularizedD Φ Ψ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (regularizedD_nonneg Φ Ψ ha))
  have hreg : regularizedD Φ Ψ = ((regularizedD Φ Ψ).toReal : EReal) :=
    (EReal.coe_toReal hfinite.ne hbot).symm
  by_contra! hlt
  obtain ⟨S, hdS, hSlim⟩ := EReal.exists_between_coe_real hlt
  have hdS' : (regularizedD Φ Ψ).toReal < S := by
    rw [hreg] at hdS
    exact EReal.coe_lt_coe_iff.mp hdS
  have hle : limsup (smoothingRate Φ Ψ ε) atTop ≤ (S : EReal) :=
    limsup_le_of_le (by isBoundedDefault) (eventually_smoothingRate_le Φ Ψ ha hfinite ε hradius S hdS')
  exact (not_lt_of_ge hle) hSlim

/-- Corollary 5.3, upper-rate half, at every fixed smoothing radius in (0,1). -/
theorem corollary_5_3_limsup_le (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    limsup (smoothingRate Φ Ψ (fun _ => ε)) atTop ≤ regularizedD Φ Ψ := by
  apply limsup_smoothingRate_le Φ Ψ ha hfinite
  intro K γ hK hγ
  have hlim : Tendsto (fun k : ℕ => K * Real.exp (-γ * k)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      TwoRateScalars.stretched_error_tendsto_zero K hγ (by norm_num : (0 : ℝ) < 1)
  exact (hlim.eventually (gt_mem_nhds hε)).mono (fun k hk => hk.le)

/-- Corollary 5.4, upper-rate half, with exactly the base-two subexponential
radius hypothesis. No monotonicity or convergence of the radii is required. -/
theorem corollary_5_4_limsup_le (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (ε : ℕ → ℝ) (εstar : ℝ)
    (hε : ∀ k, 0 < ε k ∧ ε k ≤ εstar) (_hstar : εstar < 1)
    (hsub : (fun k : ℕ => Real.log (1 / ε k) / Real.log 2) =o[atTop]
      (fun k : ℕ => (k : ℝ))) :
    limsup (smoothingRate Φ Ψ ε) atTop ≤ regularizedD Φ Ψ :=
  limsup_smoothingRate_le Φ Ψ ha hfinite ε
    (eventually_exponential_le_radius ε (fun k => (hε k).1)
      (log_inverse_isLittleO_of_base_two ε hsub))

end QuantumChannelStein.SubchannelSmoothingRates
