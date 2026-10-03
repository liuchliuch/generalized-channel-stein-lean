import QuantumChannelStein.ChannelEntropyChoi
import QuantumChannelStein.ChannelEntropyRates
import QuantumChannelStein.TensorUnit

/-!
# Channel-divergence finiteness and nonasymptotic rate bounds

For the actual channel supremum and the tensor-power supremum convention
`regularizedD`, finiteness is equivalent to Choi support inclusion and to
finite CP scalar domination. The tensor powers and the one-use identity
are proved for actual Kraus channels, not supplied as entropy hypotheses.

The supremum convention remains explicit: no claim of equality with a
limit, or of state/channel entropy additivity, is made in this file.
-/

noncomputable section
namespace QuantumChannelStein.ChannelEntropy

variable {n m : ℕ}

/-- The entropy of one actual tensor-power use is the original channel
entropy, after the proved equality of the represented linear maps. -/
theorem channelD_tensorPower_one (Φ Ψ : KrausChannel n m) :
    channelD (Φ.tensorPower 1) (Ψ.tensorPower 1) = channelD Φ Ψ := by
  rw [← channelD_cast (Φ.tensorPower 1) (Ψ.tensorPower 1) (Nat.pow_one n) (Nat.pow_one m)]
  exact channelD_congr _ Φ _ Ψ Φ.tensorPower_one_toLinearMap Ψ.tensorPower_one_toLinearMap

/-- One-use channel divergence is bounded by the exact tensor-power
regularization supremum. -/
theorem channelD_le_regularizedD (Φ Ψ : KrausChannel n m) :
    channelD Φ Ψ ≤ regularizedD Φ Ψ := by
  have h := tensorPower_rate_le_regularizedD Φ Ψ 1 (by decide)
  simpa only [Nat.cast_one, inv_one, EReal.coe_one, one_mul, channelD_tensorPower_one] using h

/-- Finiteness of the exact tensor-power supremum is equivalent to
existence of a finite one-use CP scalar domination constant. -/
theorem regularizedD_lt_top_iff_exists_cpLe (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    regularizedD Φ Ψ < ⊤ ↔
      ∃ c : ℝ, 1 ≤ c ∧ MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap) := by
  constructor
  · intro h
    apply (channelD_lt_top_iff_exists_cpLe Φ Ψ hn).mp
    exact lt_of_le_of_lt (channelD_le_regularizedD Φ Ψ) h
  · rintro ⟨c, hc, h⟩
    exact regularizedD_lt_top_of_cpLe Φ Ψ c hc h

/-- The one-use and tensor-power-supremum divergences are finite together. -/
theorem channelD_lt_top_iff_regularizedD_lt_top (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    channelD Φ Ψ < ⊤ ↔ regularizedD Φ Ψ < ⊤ := by
  rw [channelD_lt_top_iff_exists_cpLe Φ Ψ hn, regularizedD_lt_top_iff_exists_cpLe Φ Ψ hn]

/-- Choi support characterizes finiteness also under the exact tensor-power
supremum convention. -/
theorem regularizedD_lt_top_iff_choi_support (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    regularizedD Φ Ψ < ⊤ ↔
      LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin := by
  rw [regularizedD_lt_top_iff_exists_cpLe Φ Ψ hn, ← choi_support_iff_exists_cpLe]

/-- Unsupported Choi pairs have infinite tensor-power supremum divergence,
already witnessed by their one-use maximally entangled input. -/
theorem regularizedD_eq_top_of_not_choi_support (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (h : ¬ LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin) :
    regularizedD Φ Ψ = ⊤ := by
  apply top_unique
  rw [← channelD_eq_top_of_not_choi_support Φ Ψ hn h]
  exact channelD_le_regularizedD Φ Ψ

/-- Zero channel uses contribute zero divergence. -/
theorem channelD_tensorPower_zero (Φ Ψ : KrausChannel n m) :
    channelD (Φ.tensorPower 0) (Ψ.tensorPower 0) = 0 :=
  channelD_self (KrausChannel.identity 1) (by decide)

/-- Every finite-block channel divergence is at most block length times
the exact regularization supremum; this also covers infinite values. -/
theorem tensorPowerD_le_mul_regularizedD (Φ Ψ : KrausChannel n m) (k : ℕ) :
    channelD (Φ.tensorPower k) (Ψ.tensorPower k) ≤
      ((k : ℝ) : EReal) * regularizedD Φ Ψ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [channelD_tensorPower_zero, Nat.cast_zero, EReal.coe_zero, zero_mul]
  · have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
    have hkn : (0 : EReal) ≤ ((k : ℝ) : EReal) := by
      exact_mod_cast (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have h := mul_le_mul_of_nonneg_left (tensorPower_rate_le_regularizedD Φ Ψ k hk) hkn
    simpa only [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hkR, EReal.coe_one,
      one_mul] using h

/-- The nonasymptotic bounds `0 ≤ a_k ≤ k d ≤ k log₂ c` for actual
channel powers, where `d` is the explicitly defined supremum rate. -/
theorem tensorPower_bounds_of_cpLe (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) (k : ℕ) :
    0 ≤ channelD (Φ.tensorPower k) (Ψ.tensorPower k) ∧
      channelD (Φ.tensorPower k) (Ψ.tensorPower k) ≤
        ((k : ℝ) : EReal) * regularizedD Φ Ψ ∧
      ((k : ℝ) : EReal) * regularizedD Φ Ψ ≤
        ((k : ℝ) : EReal) * (Real.logb 2 c : EReal) := by
  refine ⟨channelD_nonneg _ _ (pow_pos hn k), tensorPowerD_le_mul_regularizedD Φ Ψ k, ?_⟩
  apply mul_le_mul_of_nonneg_left (regularizedD_le_log2_of_cpLe Φ Ψ c hc h)
  exact_mod_cast (Nat.cast_nonneg k : (0 : ℝ) ≤ k)

end QuantumChannelStein.ChannelEntropy
