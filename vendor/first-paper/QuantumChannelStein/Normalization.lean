import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Normalization of an approximate contraction

This file isolates genuine normed-space estimates used in the normalization step
of Corollary 5.2 of arXiv:2609.27196v1. It does not construct quantum channels,
subchannels, or Stinespring dilations. The hypotheses on the approximation are
explicit; no operator approximation theorem is assumed implicitly.
-/

namespace QuantumChannelStein.Normalization

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- Rescale an approximation by the reciprocal of one plus its error budget. -/
noncomputable def normalize (error : ℝ) (X : E) : E := (1 + error)⁻¹ • X

omit [NormedSpace ℝ E] in
/-- An `error`-approximation to a vector in the unit ball has norm at most
`1 + error`. -/
theorem norm_approx_le {V X : E} {error : ℝ}
    (hV : ‖V‖ ≤ 1) (happrox : ‖V - X‖ ≤ error) :
    ‖X‖ ≤ 1 + error := by
  calc
    ‖X‖ = ‖V - (V - X)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖V‖ + ‖V - X‖ := norm_sub_le _ _
    _ ≤ 1 + error := add_le_add hV happrox

/-- Normalizing an approximation to a contraction gives a contraction. -/
theorem norm_normalize_le_one {V X : E} {error : ℝ}
    (herror : 0 ≤ error) (hV : ‖V‖ ≤ 1) (happrox : ‖V - X‖ ≤ error) :
    ‖normalize error X‖ ≤ 1 := by
  have hden : 0 < 1 + error := by linarith
  have hinv : 0 ≤ (1 + error)⁻¹ := inv_nonneg.mpr hden.le
  rw [normalize, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
  calc
    (1 + error)⁻¹ * ‖X‖ ≤ (1 + error)⁻¹ * (1 + error) :=
      mul_le_mul_of_nonneg_left (norm_approx_le hV happrox) hinv
    _ = 1 := inv_mul_cancel₀ hden.ne'

/-- The normalized approximation has error at most `2 error / (1 + error)`.
The statement is valid in every real seminormed vector space. -/
theorem norm_sub_normalize_le {V X : E} {error : ℝ}
    (herror : 0 ≤ error) (hV : ‖V‖ ≤ 1) (happrox : ‖V - X‖ ≤ error) :
    ‖V - normalize error X‖ ≤ 2 * error / (1 + error) := by
  have hden : 0 < 1 + error := by linarith
  have hinv : 0 ≤ (1 + error)⁻¹ := inv_nonneg.mpr hden.le
  have hcoeff : (1 + error)⁻¹ * error + (1 + error)⁻¹ = 1 := by
    field_simp [hden.ne']
    ring
  have hdecomp : V - normalize error X =
      (1 + error)⁻¹ • (error • V + (V - X)) := by
    rw [normalize, smul_add, smul_sub, ← add_sub_assoc, smul_smul,
      ← add_smul, hcoeff, one_smul]
  rw [hdecomp, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
  calc
    (1 + error)⁻¹ * ‖error • V + (V - X)‖ ≤
        (1 + error)⁻¹ * (‖error • V‖ + ‖V - X‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hinv
    _ = (1 + error)⁻¹ * (error * ‖V‖ + ‖V - X‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg herror]
    _ ≤ (1 + error)⁻¹ * (error * 1 + error) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hV herror) happrox) hinv
    _ = 2 * error / (1 + error) := by ring

/-- Removing the normalization denominator gives the coarser `2 error` bound. -/
theorem double_error_div_le {error : ℝ} (herror : 0 ≤ error) :
    2 * error / (1 + error) ≤ 2 * error := by
  have hden : 0 < 1 + error := by linarith
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg error]

/-- Normalization costs at most twice the original approximation error. -/
theorem norm_sub_normalize_le_double {V X : E} {error : ℝ}
    (herror : 0 ≤ error) (hV : ‖V‖ ≤ 1) (happrox : ‖V - X‖ ≤ error) :
    ‖V - normalize error X‖ ≤ 2 * error :=
  (norm_sub_normalize_le herror hV happrox).trans (double_error_div_le herror)

/-- The normalization bounds packaged together, with the sharp and coarse errors. -/
theorem normalization_bounds {V X : E} {error : ℝ}
    (herror : 0 ≤ error) (hV : ‖V‖ ≤ 1) (happrox : ‖V - X‖ ≤ error) :
    ‖normalize error X‖ ≤ 1 ∧
      ‖V - normalize error X‖ ≤ 2 * error / (1 + error) ∧
      2 * error / (1 + error) ≤ 2 * error :=
  ⟨norm_normalize_le_one herror hV happrox,
    norm_sub_normalize_le herror hV happrox, double_error_div_le herror⟩

/-- A continuous linear contraction does not amplify a prescribed norm error. -/
theorem contraction_error_le (A : E →L[ℝ] F) {V X : E} {error : ℝ}
    (hA : ‖A‖ ≤ 1) (happrox : ‖V - X‖ ≤ error) :
    ‖A V - A X‖ ≤ error := by
  rw [← map_sub]
  have h := A.le_of_opNorm_le_of_le hA happrox
  simpa only [one_mul] using h

/-- The basic acceptance-amplitude estimate for a continuous linear contraction.
No quantum or positivity assumptions are hidden in this norm inequality. -/
theorem contraction_amplitude_le (A : E →L[ℝ] F) {V X : E} {error : ℝ}
    (hA : ‖A‖ ≤ 1) (happrox : ‖V - X‖ ≤ error) :
    ‖A V‖ ≤ ‖A X‖ + error := by
  have h := norm_sub_norm_le (A V) (A X)
  have herr := contraction_error_le A hA happrox
  linarith

/-- Apply the contraction amplitude estimate after normalization. -/
theorem contraction_normalize_amplitude_le (A : E →L[ℝ] F)
    {V X : E} {error : ℝ} (herror : 0 ≤ error) (hA : ‖A‖ ≤ 1)
    (hV : ‖V‖ ≤ 1) (happrox : ‖V - X‖ ≤ error) :
    ‖A V‖ ≤ ‖A (normalize error X)‖ + 2 * error / (1 + error) :=
  contraction_amplitude_le A hA (norm_sub_normalize_le herror hV happrox)

end QuantumChannelStein.Normalization
