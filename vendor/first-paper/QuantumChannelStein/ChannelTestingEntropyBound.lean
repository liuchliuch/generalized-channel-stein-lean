import QuantumChannelStein.BinaryDataProcessing
import QuantumChannelStein.TestingPrimal
import QuantumChannelStein.ChannelEntropyFiniteness

/-! # Entropy upper bound for actual channel testing (Lemma 4.3)

The quantity bounded here is the supremum of actual pure reference inputs
and actual binary effects, already identified with the primal SDP. The
regularization is the exact channel-divergence supremum, with actual tensor
powers. The extended-real statement also covers infinite divergence.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.TestingPrimal
open ChannelEntropy BinaryMeasurement Filter
open scoped Topology

variable {n m : ℕ}

/-- Taking the genuine attained operational maximum of the binary DPI bound. -/
theorem channelHockeyStick_le_min_of_channelD_le (Φ Ψ : KrausChannel n m)
    (hn : 0 < n) (D x : ℝ) (hx : 0 < x) (hD : channelD Φ Ψ ≤ (D : EReal)) :
    channelHockeyStick Φ Ψ ((2 : ℝ) ^ x) ≤ min 1 ((D + 1) / x) := by
  obtain ⟨ψ, T, hmax⟩ := exists_pure_maximizer Φ Ψ hn ((2 : ℝ) ^ x)
  rw [← hmax]
  exact hockeyStick_le_min_of_umegaki_le T (pureOutput Φ ψ) (pureOutput Ψ ψ) D x hx
    ((umegaki_pureOutput_le_channelD Φ Ψ ψ).trans hD)

/-- Finite-block form for any real upper bound on the actual regularized entropy. -/
theorem channelHockeyStick_tensorPower_le_of_regularizedD_le (Φ Ψ : KrausChannel n m)
    (hn : 0 < n) (d r : ℝ) (hd : regularizedD Φ Ψ ≤ (d : EReal)) (hr : 0 < r)
    (k : ℕ) (hk : 0 < k) :
    channelHockeyStick (Φ.tensorPower k) (Ψ.tensorPower k) ((2 : ℝ) ^ ((k : ℝ) * r)) ≤
      min 1 (((k : ℝ) * d + 1) / ((k : ℝ) * r)) := by
  apply channelHockeyStick_le_min_of_channelD_le _ _ (pow_pos hn k)
    ((k : ℝ) * d) ((k : ℝ) * r) (mul_pos (by exact_mod_cast hk) hr)
  calc
    channelD (Φ.tensorPower k) (Ψ.tensorPower k) ≤
        ((k : ℝ) : EReal) * regularizedD Φ Ψ := tensorPowerD_le_mul_regularizedD Φ Ψ k
    _ ≤ ((k : ℝ) : EReal) * (d : EReal) :=
      mul_le_mul_of_nonneg_left hd (EReal.coe_nonneg.mpr (Nat.cast_nonneg k))
    _ = (((k : ℝ) * d : ℝ) : EReal) := (EReal.coe_mul _ _).symm

/-- The finite-valued literal regularization gives the paper's numerical ratio. -/
theorem channelHockeyStick_tensorPower_le_finite (Φ Ψ : KrausChannel n m)
    (hn : 0 < n) (hfinite : regularizedD Φ Ψ < ⊤) (r : ℝ) (hr : 0 < r)
    (k : ℕ) (hk : 0 < k) :
    channelHockeyStick (Φ.tensorPower k) (Ψ.tensorPower k) ((2 : ℝ) ^ ((k : ℝ) * r)) ≤
      min 1 (((k : ℝ) * (regularizedD Φ Ψ).toReal + 1) / ((k : ℝ) * r)) := by
  have hbot : regularizedD Φ Ψ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (regularizedD_nonneg Φ Ψ hn))
  apply channelHockeyStick_tensorPower_le_of_regularizedD_le Φ Ψ hn _ r _ hr k hk
  rw [EReal.coe_toReal hfinite.ne hbot]

/-- **Lemma 4.3**, including the infinite-divergence branch. -/
theorem channelHockeyStick_tensorPower_le_regularizedD (Φ Ψ : KrausChannel n m)
    (hn : 0 < n) (r : ℝ) (hr : 0 < r) (k : ℕ) (hk : 0 < k) :
    (channelHockeyStick (Φ.tensorPower k) (Ψ.tensorPower k)
      ((2 : ℝ) ^ ((k : ℝ) * r)) : EReal) ≤
      min 1 ((((k : ℝ) : EReal) * regularizedD Φ Ψ + 1) / (↑((k : ℝ) * r) : EReal)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkr : 0 < (k : ℝ) * r := mul_pos hkR hr
  refine le_min ?_ ?_
  · exact_mod_cast channelHockeyStick_le_one (Φ.tensorPower k) (Ψ.tensorPower k)
      (pow_pos hn k) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
  · by_cases ht : regularizedD Φ Ψ = ⊤
    · rw [ht, EReal.coe_mul_top_of_pos hkR]
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) from rfl, EReal.top_add_coe,
        EReal.top_div_of_pos_ne_top (EReal.coe_pos.mpr hkr) (EReal.coe_ne_top _)]
      exact le_top
    · have hfinite : regularizedD Φ Ψ < ⊤ := lt_top_iff_ne_top.mpr ht
      have hbot : regularizedD Φ Ψ ≠ ⊥ :=
        ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (regularizedD_nonneg Φ Ψ hn))
      have h := (le_min_iff.mp
        (channelHockeyStick_tensorPower_le_finite Φ Ψ hn hfinite r hr k hk)).2
      have hcoe := EReal.coe_toReal ht hbot
      calc
        (channelHockeyStick (Φ.tensorPower k) (Ψ.tensorPower k)
          ((2 : ℝ) ^ ((k : ℝ) * r)) : EReal) ≤
            ((((k : ℝ) * (regularizedD Φ Ψ).toReal + 1) / ((k : ℝ) * r) : ℝ) : EReal) :=
              EReal.coe_le_coe_iff.mpr h
        _ = _ := by rw [EReal.coe_div, EReal.coe_add, EReal.coe_mul, hcoe, EReal.coe_one]

/-- Every strict finite rate gap supplies a fixed error margin below one for
all sufficiently long actual channel blocks, as used to begin amplification. -/
theorem exists_margin_eventually_channelHockeyStick_le (Φ Ψ : KrausChannel n m)
    (hn : 0 < n) (hfinite : regularizedD Φ Ψ < ⊤) (r : ℝ)
    (hr : (regularizedD Φ Ψ).toReal < r) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ᶠ k : ℕ in atTop,
        channelHockeyStick (Φ.tensorPower k) (Ψ.tensorPower k)
          ((2 : ℝ) ^ ((k : ℝ) * r)) ≤ δ ^ 2 := by
  have hd : 0 ≤ (regularizedD Φ Ψ).toReal :=
    EReal.toReal_nonneg (regularizedD_nonneg Φ Ψ hn)
  have hr0 : 0 < r := hd.trans_lt hr
  obtain ⟨δ, hδ0, hδ1, hratio⟩ :=
    BinaryEntropyBounds.exists_margin_eventually_testing_ratio_le hd hr
  refine ⟨δ, hδ0, hδ1, ?_⟩
  filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)] with k hk hk0
  exact (channelHockeyStick_tensorPower_le_finite Φ Ψ hn hfinite r hr0 k hk0).trans
    ((min_le_right _ _).trans hk)

end QuantumChannelStein.TestingPrimal
