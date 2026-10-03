import QuantumChannelStein.DiamondNormChannel
import QuantumChannelStein.ParallelExponent
import QuantumChannelStein.PseudoinverseDomination

/-!
# CP-order max-relative entropy and genuine diamond subchannel smoothing

The value is extended real, not extended nonnegative real: a nonzero
trace-decreasing map can have negative finite max-relative entropy. Its
cost is the literal infimum of positive CP-domination constants.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.MaxRelativeEntropy
open Matrix DiamondNorm ChannelEntropy
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
variable {a b : ℕ}

/-- The literal nonnegative domination cost, with empty infimum infinity. -/
def dominationCost (Φ : MatrixMap a b) (Ψ : KrausChannel a b) : ENNReal :=
  ⨅ t : {t : ℝ // 0 < t ∧ MatrixMap.CPLe Φ ((t : ℂ) • Ψ.toLinearMap)},
    ENNReal.ofReal t.val

/-- Base-two extended logarithm of the positive CP-domination cost.
For nonzero CP maps this is the paper's Dmax; the definition is total. -/
def maxRelativeEntropy (Φ : MatrixMap a b) (Ψ : KrausChannel a b) : EReal :=
  ((Real.log 2)⁻¹ : ℝ) * ENNReal.log (dominationCost Φ Ψ)

theorem dominationCost_le (Φ : MatrixMap a b) (Ψ : KrausChannel a b)
    {t : ℝ} (ht : 0 < t) (h : MatrixMap.CPLe Φ ((t : ℂ) • Ψ.toLinearMap)) :
    dominationCost Φ Ψ ≤ ENNReal.ofReal t :=
  iInf_le_of_le ⟨t, ht, h⟩ le_rfl

/-- Every actual positive CP-domination constant gives the expected Dmax bound. -/
theorem maxRelativeEntropy_le_of_cpLe (Φ : MatrixMap a b) (Ψ : KrausChannel a b)
    {t : ℝ} (ht : 0 < t) (h : MatrixMap.CPLe Φ ((t : ℂ) • Ψ.toLinearMap)) :
    maxRelativeEntropy Φ Ψ ≤ ((Real.log t / Real.log 2 : ℝ) : EReal) := by
  have hm := mul_le_mul_of_nonneg_left
    (ENNReal.log_le_log (dominationCost_le Φ Ψ ht h))
    (EReal.coe_nonneg.mpr (inv_nonneg.mpr
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le))
  rw [ENNReal.log_ofReal_of_pos ht, ← EReal.coe_mul] at hm
  convert hm using 1 <;> congr 1 <;> ring

/-- Base-two exponential domination gives its exact log-rate upper bound. -/
theorem maxRelativeEntropy_le_of_two_rpow (Φ : MatrixMap a b) (Ψ : KrausChannel a b)
    (R : ℝ) (h : MatrixMap.CPLe Φ (Complex.ofReal ((2 : ℝ) ^ R) • Ψ.toLinearMap)) :
    maxRelativeEntropy Φ Ψ ≤ (R : EReal) := by
  have hb := maxRelativeEntropy_le_of_cpLe Φ Ψ (by positivity) h
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    mul_div_cancel_right₀ R (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'] at hb
  exact hb

/-- With no positive finite domination constant the max-relative entropy is infinity. -/
theorem maxRelativeEntropy_eq_top_of_no_domination (Φ : MatrixMap a b) (Ψ : KrausChannel a b)
    (h : ∀ t : ℝ, 0 < t → ¬ MatrixMap.CPLe Φ ((t : ℂ) • Ψ.toLinearMap)) :
    maxRelativeEntropy Φ Ψ = ⊤ := by
  letI : IsEmpty {t : ℝ // 0 < t ∧ MatrixMap.CPLe Φ ((t : ℂ) • Ψ.toLinearMap)} :=
    ⟨fun t => h t.val t.property.1 t.property.2⟩
  simp only [maxRelativeEntropy, dominationCost, iInf_of_empty, ENNReal.log_top]
  exact EReal.coe_mul_top_of_pos (inv_pos.mpr (Real.log_pos (by norm_num)))

/-- Every positive domination cost bounds the real Choi trace ratio from below. -/
theorem choi_trace_ratio_le (Φ : MatrixMap a b) (Ψ : KrausChannel a b) (ha : 0 < a)
    {t : ℝ} (h : MatrixMap.CPLe Φ ((t : ℂ) • Ψ.toLinearMap)) :
    (MatrixMap.choi Φ).trace.re / (a : ℝ) ≤ t := by
  have hh := (MatrixMap.cpLe_iff_choi_difference _ _).mp h
  have ht := (Complex.nonneg_iff.mp hh.trace_nonneg).1
  simp only [MatrixMap.choi_smul, MatrixMap.choi_toLinearMap, Matrix.trace_sub,
    Matrix.trace_smul, Pseudoinverse.choi_trace, smul_eq_mul, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
    mul_zero, sub_zero] at ht
  exact (div_le_iff₀ (Nat.cast_pos.mpr ha)).mpr (by linarith)

/-- A nonzero CP map has strictly positive cost, so its Dmax cannot be minus infinity. -/
theorem dominationCost_pos (Φ : MatrixMap a b) (hΦ : MatrixMap.CompletelyPositive Φ)
    (hΦ0 : Φ ≠ 0) (Ψ : KrausChannel a b) (ha : 0 < a) : 0 < dominationCost Φ Ψ := by
  have hp := MatrixMap.choi_positive_of_completelyPositive Φ hΦ
  have hn : MatrixMap.choi Φ ≠ 0 := by
    intro h
    apply hΦ0
    apply MatrixMap.choi_injective
    simpa only [MatrixMap.choi_zero] using h
  have htr : 0 < (MatrixMap.choi Φ).trace.re :=
    (norm_pos_iff.mpr hn).trans_le (TestingSDP.positive_norm_le_trace hp)
  have hratio : 0 < (MatrixMap.choi Φ).trace.re / (a : ℝ) :=
    div_pos htr (Nat.cast_pos.mpr ha)
  apply lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hratio)
  apply le_iInf
  intro t
  exact ENNReal.ofReal_le_ofReal (choi_trace_ratio_le Φ Ψ ha t.property.2)

/-- The exact cost of a positive scalar multiple of a channel may be below one. -/
theorem dominationCost_smul_channel (Ψ : KrausChannel a b) (ha : 0 < a)
    (t : ℝ) (ht : 0 < t) :
    dominationCost ((t : ℂ) • Ψ.toLinearMap) Ψ = ENNReal.ofReal t := by
  apply le_antisymm (dominationCost_le _ Ψ ht (MatrixMap.cpLe_refl _))
  apply le_iInf
  intro u
  apply ENNReal.ofReal_le_ofReal
  have hratio := choi_trace_ratio_le ((t : ℂ) • Ψ.toLinearMap) Ψ ha u.property.2
  simpa only [MatrixMap.choi_smul, MatrixMap.choi_toLinearMap, Matrix.trace_smul,
    Pseudoinverse.choi_trace, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero,
    mul_div_cancel_right₀ t (Nat.cast_ne_zero.mpr ha.ne')] using hratio

theorem maxRelativeEntropy_smul_channel (Ψ : KrausChannel a b) (ha : 0 < a)
    (t : ℝ) (ht : 0 < t) :
    maxRelativeEntropy ((t : ℂ) • Ψ.toLinearMap) Ψ =
      ((Real.log t / Real.log 2 : ℝ) : EReal) := by
  rw [maxRelativeEntropy, dominationCost_smul_channel Ψ ha t ht,
    ENNReal.log_ofReal_of_pos ht, ← EReal.coe_mul]
  congr 1
  ring

/-- Nonzero completely positive maps cannot acquire a spurious minus-infinite value. -/
theorem maxRelativeEntropy_ne_bot (Φ : MatrixMap a b) (hΦ : MatrixMap.CompletelyPositive Φ)
    (hΦ0 : Φ ≠ 0) (Ψ : KrausChannel a b) (ha : 0 < a) :
    maxRelativeEntropy Φ Ψ ≠ ⊥ := by
  apply (EReal.mul_ne_bot _ _).mpr
  refine ⟨Or.inl (by simp), Or.inr ?_, Or.inl (by simp), Or.inl ?_⟩
  · exact ne_of_gt (ENNReal.bot_lt_log_iff.mpr (dominationCost_pos Φ hΦ hΦ0 Ψ ha))
  · exact EReal.coe_nonneg.mpr (inv_nonneg.mpr (Real.log_pos (by norm_num)).le)

/-- Scaling down a genuine channel gives an actual trace-decreasing subchannel. -/
def scaledChannel (Ψ : KrausChannel a b) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Subchannel a b where
  toLinearMap := (t : ℂ) • Ψ.toLinearMap
  completelyPositive := MatrixMap.completelyPositive_smul ht (MatrixMap.completelyPositive_toLinearMap Ψ)
  trace_nonincreasing := by
    intro X hX
    change ((t : ℂ) • Ψ.apply X).trace.re ≤ X.trace.re
    rw [Matrix.trace_smul, Ψ.trace_apply]
    simpa only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using
      mul_le_of_le_one_left (Complex.nonneg_iff.mp hX.trace_nonneg).1 ht1

/-- Negative finite Dmax values really occur for nonzero subchannels. -/
theorem maxRelativeEntropy_scaledChannel_neg (Ψ : KrausChannel a b) (ha : 0 < a)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    maxRelativeEntropy (scaledChannel Ψ t ht.le ht1.le).toLinearMap Ψ < 0 := by
  rw [show (scaledChannel Ψ t ht.le ht1.le).toLinearMap = (t : ℂ) • Ψ.toLinearMap from rfl,
    maxRelativeEntropy_smul_channel Ψ ha t ht]
  exact EReal.coe_lt_coe_iff.mpr
    (div_neg_of_neg_of_pos (Real.log_neg ht ht1) (Real.log_pos (by norm_num)))

/-- Equation (5.2): actual diamond-feasible CP/TNI subchannels, with an
extended-real infimum so negative finite values and empty sets are retained. -/
def smoothedMaxRelativeEntropy (Φ Ψ : KrausChannel a b) (ε : ℝ) : EReal :=
  ⨅ L : {L : Subchannel a b // diamondNorm (L.toLinearMap - Φ.toLinearMap) ≤ ENNReal.ofReal ε},
    maxRelativeEntropy L.val.toLinearMap Ψ

theorem smoothedMaxRelativeEntropy_le (Φ Ψ : KrausChannel a b) (ε : ℝ)
    (L : Subchannel a b) (hL : diamondNorm (L.toLinearMap - Φ.toLinearMap) ≤ ENNReal.ofReal ε) :
    smoothedMaxRelativeEntropy Φ Ψ ε ≤ maxRelativeEntropy L.toLinearMap Ψ :=
  iInf_le_of_le ⟨L, hL⟩ le_rfl

/-- The zero map is not silently admitted to the smoothing optimization. -/
theorem smoothed_feasible_nonzero (Φ : KrausChannel a b) (ha : 0 < a) (ε : ℝ) (hε : ε < 1)
    (L : Subchannel a b) (hL : diamondNorm (L.toLinearMap - Φ.toLinearMap) ≤ ENNReal.ofReal ε) :
    L.toLinearMap ≠ 0 := nonzero_of_diamond_close Φ ha L.toLinearMap ε hε hL

/-- Larger smoothing radii enlarge the genuine feasible set. -/
theorem smoothedMaxRelativeEntropy_antitone (Φ Ψ : KrausChannel a b) :
    Antitone (smoothedMaxRelativeEntropy Φ Ψ) := by
  intro ε δ hεδ
  apply le_iInf
  intro L
  exact smoothedMaxRelativeEntropy_le Φ Ψ δ L.val
    (L.property.trans (ENNReal.ofReal_le_ofReal hεδ))

end QuantumChannelStein.MaxRelativeEntropy
