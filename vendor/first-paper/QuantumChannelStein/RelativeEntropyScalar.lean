import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Scalar Klein inequality and doubly stochastic finite sums

The support hypothesis handles zero eigenvalues without pretending the
unrestricted, totalized logarithm defines relative entropy there.
-/

noncomputable section
namespace QuantumChannelStein.RelativeEntropy

open scoped BigOperators

/-- The scalar Klein inequality, including a zero first argument. -/
theorem scalar_klein_ln {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p - q ≤ p * (Real.log p - Real.log q) := by
  rcases eq_or_lt_of_le hp with hp0 | hp
  · subst p
    simp only [zero_sub, zero_mul]
    exact neg_nonpos.mpr hq.le
  · have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hq hp)) hp.le
    rw [Real.log_div hq.ne' hp.ne'] at h
    have heq : p * (q / p - 1) = q - p := by
      field_simp
    rw [heq] at h
    nlinarith

/-- A weighted scalar Klein inequality with explicit support compatibility. -/
theorem weighted_scalar_klein_ln {p q w : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hw : 0 ≤ w)
    (hzero : q = 0 → p * w = 0) :
    w * (p - q) ≤ w * (p * (Real.log p - Real.log q)) := by
  rcases eq_or_lt_of_le hq with hq0 | hq
  · have hwp : w * p = 0 := by simpa [mul_comm] using hzero hq0.symm
    simp [← hq0, ← mul_assoc, hwp]
  · exact mul_le_mul_of_nonneg_left (scalar_klein_ln hp hq) hw

/-- Klein nonnegativity for two probability lists and a doubly stochastic
change-of-eigenbasis weight matrix, in natural-logarithm units. -/
theorem doubly_stochastic_klein_ln {n : ℕ} (p q : Fin n → ℝ)
    (w : Fin n → Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ j, q j = 1)
    (hw : ∀ i j, 0 ≤ w i j)
    (hwrow : ∀ i, ∑ j, w i j = 1)
    (hwcol : ∀ j, ∑ i, w i j = 1)
    (hzero : ∀ i j, q j = 0 → p i * w i j = 0) :
    0 ≤ ∑ i, ∑ j, w i j * (p i * (Real.log (p i) - Real.log (q j))) := by
  have hp' : (∑ i, ∑ j, w i j * p i) = 1 := by
    simp_rw [← Finset.sum_mul, hwrow, one_mul]
    exact hpsum
  have hq' : (∑ i, ∑ j, w i j * q j) = 1 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hwcol, one_mul]
    exact hqsum
  have hlower : (∑ i, ∑ j, w i j * (p i - q j)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [hp', hq', sub_self]
  rw [← hlower]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    weighted_scalar_klein_ln (hp i) (hq j) (hw i j) (hzero i j)

/-- The same finite weighted Klein inequality in bits. -/
theorem doubly_stochastic_klein_log2 {n : ℕ} (p q : Fin n → ℝ)
    (w : Fin n → Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ j, q j = 1)
    (hw : ∀ i j, 0 ≤ w i j)
    (hwrow : ∀ i, ∑ j, w i j = 1)
    (hwcol : ∀ j, ∑ i, w i j = 1)
    (hzero : ∀ i j, q j = 0 → p i * w i j = 0) :
    0 ≤ ∑ i, ∑ j, w i j * (p i * (Real.logb 2 (p i) - Real.logb 2 (q j))) := by
  have hn := doubly_stochastic_klein_ln p q w hp hq hpsum hqsum hw hwrow hwcol hzero
  have htwo : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hdiv := div_nonneg hn htwo
  simpa only [Real.logb, ← sub_div, mul_div_assoc, Finset.sum_div] using hdiv

end QuantumChannelStein.RelativeEntropy
