import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-! Scalar estimates for the actual Chebyshev filter in Lemma 29 of arXiv:2609.30762. -/
noncomputable section
namespace GeneralizedChannelStein.ImageProjectorScalars
open Polynomial Real

def filterDegree (k ξ : ℝ) : ℕ := ⌈Real.sqrt k * Real.log (2 / ξ)⌉₊
def denominator (k : ℝ) (ℓ : ℕ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (ℓ : ℤ)).eval ((k + 1) / (k - 1))

theorem chebyshev_abs_le_one (ℓ : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(Polynomial.Chebyshev.T ℝ (ℓ : ℤ)).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

private theorem sqrt_gt_one {k : ℝ} (hk : 2 ≤ k) : 1 < Real.sqrt k := by
  have hs := Real.sq_sqrt (show 0 ≤ k by linarith)
  have hn := Real.sqrt_nonneg k
  nlinarith

theorem cosh_log_ratio {k : ℝ} (hk : 2 ≤ k) :
    Real.cosh (Real.log ((Real.sqrt k + 1) / (Real.sqrt k - 1))) =
      (k + 1) / (k - 1) := by
  have hs := sqrt_gt_one hk
  have hsq := Real.sq_sqrt (show 0 ≤ k by linarith)
  have hm : 0 < Real.sqrt k - 1 := by linarith
  have hp : 0 < Real.sqrt k + 1 := by linarith
  have hk1 : 0 < k - 1 := by linarith
  rw [Real.cosh_log (div_pos hp hm)]
  field_simp
  nlinarith [sq_nonneg (Real.sqrt k)]

theorem inv_sqrt_le_log_ratio {k : ℝ} (hk : 2 ≤ k) :
    1 / Real.sqrt k ≤ Real.log ((Real.sqrt k + 1) / (Real.sqrt k - 1)) := by
  have hs := sqrt_gt_one hk
  have hm : 0 < Real.sqrt k - 1 := by linarith
  have hp : 0 < Real.sqrt k + 1 := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos
    (div_pos hp hm)
  apply le_trans _ hlog
  rw [inv_div]
  field_simp
  nlinarith

theorem denominator_eq_cosh {k : ℝ} (hk : 2 ≤ k) (ℓ : ℕ) :
    denominator k ℓ = Real.cosh ((ℓ : ℝ) *
      Real.log ((Real.sqrt k + 1) / (Real.sqrt k - 1))) := by
  unfold denominator
  rw [← cosh_log_ratio hk, Polynomial.Chebyshev.T_real_cosh]
  norm_cast

theorem one_le_denominator {k : ℝ} (hk : 2 ≤ k) (ℓ : ℕ) :
    1 ≤ denominator k ℓ := by
  rw [denominator_eq_cosh hk]
  rw [Real.cosh_eq]
  have h := Real.add_one_le_exp (((ℓ : ℝ) * Real.log ((Real.sqrt k + 1) / (Real.sqrt k - 1))))
  have h' := Real.add_one_le_exp (-((ℓ : ℝ) * Real.log ((Real.sqrt k + 1) / (Real.sqrt k - 1))))
  linarith

theorem exp_half_le_denominator {k : ℝ} (hk : 2 ≤ k) (ℓ : ℕ) :
    Real.exp ((ℓ : ℝ) / Real.sqrt k) / 2 ≤ denominator k ℓ := by
  have h := mul_le_mul_of_nonneg_left (inv_sqrt_le_log_ratio hk)
    (show 0 ≤ (ℓ : ℝ) by positivity)
  have he := Real.exp_le_exp.mpr h
  rw [denominator_eq_cosh hk, Real.cosh_eq]
  simp only [mul_one_div] at he
  linarith [Real.exp_pos (-((ℓ : ℝ) *
    Real.log ((Real.sqrt k + 1) / (Real.sqrt k - 1))))]

theorem reciprocal_denominator_le {k ξ : ℝ} (hk : 2 ≤ k) (hξ : 0 < ξ) :
    (denominator k (filterDegree k ξ))⁻¹ ≤ ξ := by
  have hs : 0 < Real.sqrt k := lt_trans (by norm_num) (sqrt_gt_one hk)
  have hc : Real.sqrt k * Real.log (2 / ξ) ≤ (filterDegree k ξ : ℝ) :=
    Nat.le_ceil _
  have hl : Real.log (2 / ξ) ≤ (filterDegree k ξ : ℝ) / Real.sqrt k := by
    apply (le_div_iff₀ hs).2
    simpa [mul_comm] using hc
  have he : 2 / ξ ≤ Real.exp ((filterDegree k ξ : ℝ) / Real.sqrt k) := by
    rw [← Real.exp_log (show 0 < 2 / ξ by positivity)]
    exact Real.exp_le_exp.mpr hl
  have hd := exp_half_le_denominator hk (filterDegree k ξ)
  have hdpos : 0 < denominator k (filterDegree k ξ) :=
    lt_of_lt_of_le (by norm_num) (one_le_denominator hk _)
  rw [inv_eq_one_div, div_le_iff₀ hdpos]
  have htwo : 2 ≤ ξ * Real.exp ((filterDegree k ξ : ℝ) / Real.sqrt k) := by
    exact (div_le_iff₀ hξ).1 he |>.trans_eq (mul_comm _ _)
  nlinarith [mul_le_mul_of_nonneg_left hd hξ.le]

/-- The exact paper range is a specialization of the stronger positive-error estimate. -/
theorem reciprocal_denominator_le_paper {k ξ : ℝ} (hk : 2 ≤ k)
    (hξ : 0 < ξ) (_hξupper : ξ ≤ 1 / 16) :
    (denominator k (filterDegree k ξ))⁻¹ ≤ ξ :=
  reciprocal_denominator_le hk hξ

theorem affine_argument_mem_Icc {k z : ℝ} (hk : 2 ≤ k)
    (hz : z ∈ Set.Icc 1 k) :
    (k + 1 - 2 * z) / (k - 1) ∈ Set.Icc (-1) 1 := by
  have h : 0 < k - 1 := by linarith
  constructor
  · apply (le_div_iff₀ h).2
    linarith [hz.2]
  · apply (div_le_iff₀ h).2
    linarith [hz.1]

theorem filter_at_zero {k : ℝ} (hk : 2 ≤ k) (ℓ : ℕ) :
    (Polynomial.Chebyshev.T ℝ (ℓ : ℤ)).eval ((k + 1 - 2 * 0) / (k - 1)) /
      denominator k ℓ = 1 := by
  simpa [denominator] using div_self
    (show denominator k ℓ ≠ 0 from ne_of_gt
      (lt_of_lt_of_le (by norm_num) (one_le_denominator hk ℓ)))

theorem abs_filter_le_error {k ξ z : ℝ} (hk : 2 ≤ k) (hξ : 0 < ξ)
    (hz : z ∈ Set.Icc 1 k) :
    |(Polynomial.Chebyshev.T ℝ (filterDegree k ξ : ℤ)).eval
      ((k + 1 - 2 * z) / (k - 1)) / denominator k (filterDegree k ξ)| ≤ ξ := by
  have hd : 0 < denominator k (filterDegree k ξ) :=
    lt_of_lt_of_le (by norm_num) (one_le_denominator hk _)
  rw [abs_div, abs_of_pos hd]
  calc
    _ ≤ 1 / denominator k (filterDegree k ξ) :=
      div_le_div_of_nonneg_right
        (chebyshev_abs_le_one _ (affine_argument_mem_Icc hk hz)) hd.le
    _ ≤ ξ := by simpa [one_div] using reciprocal_denominator_le hk hξ

end GeneralizedChannelStein.ImageProjectorScalars
