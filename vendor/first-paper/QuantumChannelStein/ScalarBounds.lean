import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar bounds used in the channel Stein argument

These are real-variable consequences of explicitly stated hypotheses. In particular,
this file does **not** formalize quantum channels, Stinespring approximation, the
sandwiched Rényi chain rule, or the full channel Stein theorem.

The acceptance-amplitude hypothesis below is the scalar conclusion of Lemma 3.4
of arXiv:2609.27196v1. The exponential bound is the scalar estimate in the proof
of Proposition 3.5. A further bound isolates the logarithmic rearrangement in the
adaptive converse (Section 3.4). Natural logarithms are used throughout, so every
base-two rate carries the factor `Real.log 2`.
-/

namespace QuantumChannelStein.ScalarBounds

/-- Squaring an acceptance-amplitude bound. No operator statement is asserted. -/
theorem acceptance_le_square {p q a error : ℝ}
    (h : Real.sqrt p ≤ a * Real.sqrt q + error) :
    p ≤ (a * Real.sqrt q + error) ^ 2 :=
  (Real.sqrt_le_iff.mp h).2

/-- Two exponential decays are bounded by their slower rate. -/
theorem exp_sum_le {n a b K : ℝ} (hn : 0 ≤ n) (hK : 0 ≤ K) :
    Real.exp (-a * n) + K * Real.exp (-b * n) ≤
      (1 + K) * Real.exp (-min a b * n) := by
  have ha : Real.exp (-a * n) ≤ Real.exp (-min a b * n) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left a b) hn]
  have hb : Real.exp (-b * n) ≤ Real.exp (-min a b * n) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (min_le_right a b) hn]
  calc
    Real.exp (-a * n) + K * Real.exp (-b * n) ≤
        Real.exp (-min a b * n) + K * Real.exp (-min a b * n) :=
      add_le_add ha (mul_le_mul_of_nonneg_left hb hK)
    _ = (1 + K) * Real.exp (-min a b * n) := by ring

/-- Squared version of the two-decay bound used in Proposition 3.5. -/
theorem exp_sum_sq_le {n a b K : ℝ} (hn : 0 ≤ n) (hK : 0 ≤ K) :
    (Real.exp (-a * n) + K * Real.exp (-b * n)) ^ 2 ≤
      (1 + K) ^ 2 * Real.exp (-2 * min a b * n) := by
  calc
    (Real.exp (-a * n) + K * Real.exp (-b * n)) ^ 2 ≤
        ((1 + K) * Real.exp (-min a b * n)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (exp_sum_le hn hK)
    _ = (1 + K) ^ 2 * Real.exp (-2 * min a b * n) := by
      rw [mul_pow]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

/-- The scalar exponential acceptance bound from the proof of Proposition 3.5.

The operator-norm approximation and testing arguments are assumptions here,
expressed only as bounds on the real numbers `a`, `error`, `p`, and `q`.
The real variable `n` may in particular be a natural blocklength cast to `ℝ`.
-/
theorem acceptance_le_exponential
    {p q a error n S R K gamma : ℝ}
    (hn : 0 ≤ n) (hK : 0 ≤ K)
    (ha : a ≤ Real.exp (n * S * Real.log 2 / 2))
    (hq : q ≤ Real.exp (-n * R * Real.log 2))
    (he : error ≤ K * Real.exp (-gamma * n))
    (hamp : Real.sqrt p ≤ a * Real.sqrt q + error) :
    p ≤ (1 + K) ^ 2 *
      Real.exp (-2 * min ((R - S) * Real.log 2 / 2) gamma * n) := by
  have hmain : a * Real.sqrt q ≤
      Real.exp (-((R - S) * Real.log 2 / 2) * n) := by
    calc
      a * Real.sqrt q ≤
          Real.exp (n * S * Real.log 2 / 2) * Real.sqrt q :=
        mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg q)
      _ ≤ Real.exp (n * S * Real.log 2 / 2) *
          Real.sqrt (Real.exp (-n * R * Real.log 2)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hq) (Real.exp_pos _).le
      _ = Real.exp (-((R - S) * Real.log 2 / 2) * n) := by
        rw [← Real.exp_half, ← Real.exp_add]
        congr 1
        ring
  have hsum : Real.sqrt p ≤
      Real.exp (-((R - S) * Real.log 2 / 2) * n) +
        K * Real.exp (-gamma * n) :=
    hamp.trans (add_le_add hmain he)
  exact (Real.sqrt_le_iff.mp hsum).2.trans (exp_sum_sq_le hn hK)

/-- The same scalar acceptance bound, starting from the squared amplification
bound used in the statement of the paper's approximation theorem. -/
theorem acceptance_le_exponential_of_sq_bound
    {p q a error n S R K gamma : ℝ}
    (hn : 0 ≤ n) (hK : 0 ≤ K)
    (ha : a ^ 2 ≤ Real.exp (n * S * Real.log 2))
    (hq : q ≤ Real.exp (-n * R * Real.log 2))
    (he : error ≤ K * Real.exp (-gamma * n))
    (hamp : Real.sqrt p ≤ a * Real.sqrt q + error) :
    p ≤ (1 + K) ^ 2 *
      Real.exp (-2 * min ((R - S) * Real.log 2 / 2) gamma * n) := by
  apply acceptance_le_exponential hn hK _ hq he hamp
  simpa only [← Real.exp_half] using Real.le_sqrt_of_sq_le ha

/-- The parallel decay rate is strictly positive for a strict rate gap. -/
theorem parallel_decay_rate_pos {R S gamma : ℝ}
    (hSR : S < R) (hgamma : 0 < gamma) :
    0 < 2 * min ((R - S) * Real.log 2 / 2) gamma := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgap : 0 < (R - S) * Real.log 2 / 2 :=
    div_pos (mul_pos (sub_pos.mpr hSR) hlog) (by norm_num)
  exact mul_pos (by norm_num) (lt_min hgap hgamma)

/-- Positivity of the scalar adaptive exponent appearing in Section 3.4. -/
theorem adaptive_decay_rate_pos {alpha R d : ℝ}
    (halpha : 1 < alpha) (hgap : d < R) :
    0 < ((alpha - 1) / alpha) * (R - d) := by
  exact mul_pos (div_pos (sub_pos.mpr halpha) (by linarith)) (sub_pos.mpr hgap)

/-- Scalar adaptive-converse rearrangement, stated with natural logarithms.

`hdiv` is the numerical inequality obtained after the quantum chain rule and
binary-measurement data processing. Those operator results are not proved here.
-/
theorem adaptive_acceptance_le_exponential
    {p q n R d alpha : ℝ}
    (hp : 0 < p) (hq : 0 < q) (halpha : 1 < alpha)
    (hdiv : alpha / (alpha - 1) * Real.log p - Real.log q ≤ n * d * Real.log 2)
    (htypeII : q ≤ Real.exp (-n * R * Real.log 2)) :
    p ≤ Real.exp (-n * ((alpha - 1) / alpha) * (R - d) * Real.log 2) := by
  have hqlog : Real.log q ≤ -n * R * Real.log 2 :=
    (Real.log_le_iff_le_exp hq).mpr htypeII
  have ha : 0 < alpha := by linarith
  have ha1 : 0 < alpha - 1 := by linarith
  have hratio : 0 < alpha / (alpha - 1) := div_pos ha ha1
  have hlinear : alpha / (alpha - 1) * Real.log p ≤
      -n * (R - d) * Real.log 2 := by
    nlinarith [hdiv, hqlog]
  apply (Real.log_le_iff_le_exp hp).mp
  apply (mul_le_mul_iff_right₀ hratio).mp
  calc
    alpha / (alpha - 1) * Real.log p ≤ -n * (R - d) * Real.log 2 := hlinear
    _ = alpha / (alpha - 1) *
        (-n * ((alpha - 1) / alpha) * (R - d) * Real.log 2) := by
      field_simp [ha.ne', ha1.ne']

/-- Uniform domination of a sum by the larger of two exponential rates.
This is the scalar maximum-of-rates step in the proof of inequality (3.6). -/
theorem exp_sum_le_max_rate {n u₀ u₁ C₀ C₁ : ℝ}
    (hn : 0 ≤ n) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) :
    C₀ * Real.exp (n * u₀) + C₁ * Real.exp (n * u₁) ≤
      (C₀ + C₁) * Real.exp (n * max u₀ u₁) := by
  have h₀ : Real.exp (n * u₀) ≤ Real.exp (n * max u₀ u₁) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_max_left u₀ u₁) hn)
  have h₁ : Real.exp (n * u₁) ≤ Real.exp (n * max u₀ u₁) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_max_right u₀ u₁) hn)
  calc
    C₀ * Real.exp (n * u₀) + C₁ * Real.exp (n * u₁) ≤
        C₀ * Real.exp (n * max u₀ u₁) + C₁ * Real.exp (n * max u₀ u₁) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ hC₀) (mul_le_mul_of_nonneg_left h₁ hC₁)
    _ = (C₀ + C₁) * Real.exp (n * max u₀ u₁) := by ring

/-- An explicit constant remainder replaces the paper's `O(1)` notation in the
logarithm-of-a-sum estimate. -/
theorem log_le_max_rate_add_constant {y n u₀ u₁ C₀ C₁ : ℝ}
    (hy : 0 < y) (hn : 0 ≤ n) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hC : 0 < C₀ + C₁)
    (hbound : y ≤ C₀ * Real.exp (n * u₀) + C₁ * Real.exp (n * u₁)) :
    Real.log y ≤ n * max u₀ u₁ + Real.log (C₀ + C₁) := by
  calc
    Real.log y ≤ Real.log ((C₀ + C₁) * Real.exp (n * max u₀ u₁)) :=
      Real.log_le_log hy (hbound.trans (exp_sum_le_max_rate hn hC₀ hC₁))
    _ = n * max u₀ u₁ + Real.log (C₀ + C₁) := by
      rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring

/-- An explicit blocklength threshold at which a positive exponential upper
bound is smaller than a prescribed positive acceptance probability. -/
theorem exponential_lt_of_threshold {C c delta n : ℝ}
    (hC : 0 < C) (hc : 0 < c) (hdelta : 0 < delta)
    (hn : (Real.log C - Real.log delta) / c < n) :
    C * Real.exp (-c * n) < delta := by
  have h : Real.log C - c * n < Real.log delta := by
    have := (div_lt_iff₀ hc).mp hn
    nlinarith
  calc
    C * Real.exp (-c * n) = Real.exp (Real.log C - c * n) := by
      rw [show Real.log C - c * n = Real.log C + (-c * n) by ring,
        Real.exp_add, Real.exp_log hC]
    _ < Real.exp (Real.log delta) := Real.exp_lt_exp.mpr h
    _ = delta := Real.exp_log hdelta


/-- Sharp scalar hockey-stick bound behind Proposition 4.2: a bounded
acceptance amplitude can increase by at most `error` under approximation. -/
theorem amplitude_hockeyStick_bound {a b error : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
    (he : 0 ≤ error) (he1 : error ≤ 1) (hamp : a ≤ b + error) :
    a ^ 2 - b ^ 2 ≤ 2 * error - error ^ 2 := by
  by_cases hsmall : a ≤ error
  · nlinarith [sq_nonneg b,
      mul_nonneg (sub_nonneg.mpr hsmall) (add_nonneg ha he),
      mul_nonneg he (sub_nonneg.mpr he1)]
  · have hdiff : 0 ≤ a - error := by linarith
    have hbdiff : a - error ≤ b := by linarith
    have hsq := (sq_le_sq₀ hdiff hb).mpr hbdiff
    nlinarith [mul_nonneg he (sub_nonneg.mpr ha1)]

/-- Probability-level form of the sharp scalar upper bound. The quantum
approximation-to-amplitude argument is a separate theorem. -/
theorem probability_hockeyStick_bound {p q t error : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (he : 0 ≤ error) (he1 : error ≤ 1)
    (hamp : Real.sqrt p ≤ Real.sqrt t * Real.sqrt q + error) :
    p - t * q ≤ 2 * error - error ^ 2 := by
  have hsqrt : Real.sqrt p ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hp1
  have h := amplitude_hockeyStick_bound (Real.sqrt_nonneg p) hsqrt
    (mul_nonneg (Real.sqrt_nonneg t) (Real.sqrt_nonneg q)) he he1 hamp
  simpa only [mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq, Real.sq_sqrt ht] using h

end QuantumChannelStein.ScalarBounds

