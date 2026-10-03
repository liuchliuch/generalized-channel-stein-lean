import QuantumChannelStein.RelativeEntropyScalar

/-!
# A finite scalar upper bound for relative entropy

The support condition explicitly removes contributions from zero denominators.
The upper bound follows from `log x ≤ x - 1` and a rowwise reciprocal bound.
-/

noncomputable section
namespace QuantumChannelStein.RelativeEntropy

open scoped BigOperators

/-- An upper logarithm bound with nonnegative weights and explicit support. -/
theorem weighted_scalar_log_upper_ln {p q w c : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hw : 0 ≤ w) (hc : 0 < c)
    (hzero : q = 0 → p * w = 0) :
    w * (p * (Real.log p - Real.log q)) ≤
      (p * w) * Real.log c + p * ((p * w / q) / c - w) := by
  rcases eq_or_lt_of_le hp with hp0 | hp
  · subst p
    simp
  rcases eq_or_lt_of_le hq with hq0 | hq
  · have hw0 : w = 0 := (mul_eq_zero.mp (hzero hq0.symm)).resolve_left hp.ne'
    simp [hw0]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp (mul_pos hc hq))
  rw [Real.log_div hp.ne' (mul_ne_zero hc.ne' hq.ne'),
    Real.log_mul hc.ne' hq.ne'] at hlog
  have hlog' : Real.log p - Real.log q ≤ Real.log c + (p / (c * q) - 1) := by
    linarith
  have h := mul_le_mul_of_nonneg_left hlog' (mul_nonneg hp.le hw)
  convert h using 1 <;> field_simp

/-- Row-stochastic scalar entropy is bounded by a rowwise reciprocal bound,
in natural-logarithm units. -/
theorem row_stochastic_entropy_upper_ln {n : ℕ} (p q : Fin n → ℝ)
    (w : Fin n → Fin n → ℝ) (c : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpsum : ∑ i, p i = 1) (hw : ∀ i j, 0 ≤ w i j)
    (hwrow : ∀ i, ∑ j, w i j = 1) (hc : 1 ≤ c)
    (hzero : ∀ i j, q j = 0 → p i * w i j = 0)
    (hinv : ∀ i, ∑ j, p i * w i j / q j ≤ c) :
    (∑ i, ∑ j, w i j * (p i * (Real.log (p i) - Real.log (q j)))) ≤
      Real.log c := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hrow : ∀ i, (∑ j, w i j * (p i * (Real.log (p i) - Real.log (q j)))) ≤
      p i * Real.log c := by
    intro i
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      weighted_scalar_log_upper_ln (hp i) (hq j) (hw i j) hcpos (hzero i j))
    have hinv' : (∑ j, p i * w i j / q j) / c - 1 ≤ 0 := by
      have hh : (∑ j, p i * w i j / q j) / c ≤ 1 :=
        (div_le_one hcpos).mpr (hinv i)
      linarith
    have hrhs : (∑ j, ((p i * w i j) * Real.log c +
        p i * ((p i * w i j / q j) / c - w i j))) =
        p i * Real.log c + p i * ((∑ j, p i * w i j / q j) / c - 1) := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, hwrow]
      ring
    rw [hrhs] at hs
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (hp i) hinv'
    linarith
  calc
    _ ≤ ∑ i, p i * Real.log c := Finset.sum_le_sum fun i _ => hrow i
    _ = Real.log c := by rw [← Finset.sum_mul, hpsum, one_mul]

/-- Row-stochastic scalar entropy in bits is bounded by a rowwise reciprocal
bound. No column-stochastic or normalization hypothesis on `q` is needed. -/
theorem row_stochastic_entropy_upper_log2 {n : ℕ} (p q : Fin n → ℝ)
    (w : Fin n → Fin n → ℝ) (c : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpsum : ∑ i, p i = 1) (hw : ∀ i j, 0 ≤ w i j)
    (hwrow : ∀ i, ∑ j, w i j = 1) (hc : 1 ≤ c)
    (hzero : ∀ i j, q j = 0 → p i * w i j = 0)
    (hinv : ∀ i, ∑ j, p i * w i j / q j ≤ c) :
    (∑ i, ∑ j, w i j * (p i * (Real.logb 2 (p i) - Real.logb 2 (q j)))) ≤
      Real.logb 2 c := by
  have hn := row_stochastic_entropy_upper_ln p q w c hp hq hpsum hw hwrow hc hzero hinv
  have htwo : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hdiv := div_le_div_of_nonneg_right hn htwo
  simpa only [Real.logb, ← sub_div, mul_div_assoc, Finset.sum_div] using hdiv

end QuantumChannelStein.RelativeEntropy
