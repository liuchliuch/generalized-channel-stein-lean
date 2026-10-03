import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Binary relative-entropy bounds for the testing estimate

These scalar estimates implement the numerical step in Lemma 4.3 of
arXiv:2609.27196v1. The binary relative entropy is written as a difference of
base-two logarithms, matching the actual spectral trace of binary diagonal
states. Its endpoint values use the convention `0 * log 0 = 0`.

The testing bound below explicitly assumes support compatibility at `q = 0`,
or derives it from `p ≤ c*q`. No finite quantum relative entropy, data-processing
inequality, or channel bound is assumed to have been proved by this file.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.BinaryEntropyBounds
open Filter Topology

/-- Binary relative entropy in bits, in the difference-log form produced by
spectral diagonalization. At a zero alternative probability this totalized
scalar expression only models relative entropy under a support hypothesis. -/
def binaryRelativeEntropy (p q : ℝ) : ℝ :=
  p * (Real.logb 2 p - Real.logb 2 q) +
    (1 - p) * (Real.logb 2 (1 - p) - Real.logb 2 (1 - q))

@[simp] theorem binaryRelativeEntropy_zero (q : ℝ) :
    binaryRelativeEntropy 0 q = -Real.logb 2 (1 - q) := by
  simp [binaryRelativeEntropy]

@[simp] theorem binaryRelativeEntropy_one (q : ℝ) :
    binaryRelativeEntropy 1 q = -Real.logb 2 q := by
  simp [binaryRelativeEntropy]

/-- A zero first argument causes no difficulty when converting weighted logs
of quotients into differences. -/
theorem weighted_logb_div (p q : ℝ) (hq : q ≠ 0) :
    p * Real.logb 2 (p / q) = p * (Real.logb 2 p - Real.logb 2 q) := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [Real.logb_div hp hq]

/-- The quotient formula agrees with the spectral difference formula for an
interior alternative probability, including both endpoints of `p`. -/
theorem binaryRelativeEntropy_eq_quotient (p : ℝ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    binaryRelativeEntropy p q = p * Real.logb 2 (p / q) +
      (1 - p) * Real.logb 2 ((1 - p) / (1 - q)) := by
  rw [weighted_logb_div p q hq0.ne',
    weighted_logb_div (1 - p) (1 - q) (sub_pos.mpr hq1).ne']
  rfl

/-- Mathlib's genuine binary-entropy maximum, converted from nats to bits. -/
theorem binaryEntropyBits_le_one (p : ℝ) : Real.binEntropy p / Real.log 2 ≤ 1 := by
  apply (div_le_one (Real.log_pos (by norm_num))).mpr
  exact Real.binEntropy_le_log_two

/-- Binary entropy in bits is nonnegative on the closed probability interval. -/
theorem binaryEntropyBits_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ Real.binEntropy p / Real.log 2 :=
  div_nonneg (Real.binEntropy_nonneg hp0 hp1) (Real.log_pos (by norm_num)).le

/-- The entropy decomposition is an exact identity even at `p=0` and `p=1`. -/
theorem binaryRelativeEntropy_eq_entropy (p q : ℝ) :
    binaryRelativeEntropy p q = -p * Real.logb 2 q -
      (1 - p) * Real.logb 2 (1 - q) - Real.binEntropy p / Real.log 2 := by
  unfold binaryRelativeEntropy Real.logb Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

/-- The standard binary testing lower bound. The entropy contribution is
bounded by one bit using `Real.binEntropy_le_log_two`. -/
theorem binaryRelativeEntropy_lower_bound {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    p * Real.logb 2 (1 / q) - 1 ≤ binaryRelativeEntropy p q := by
  have hcomp : Real.logb 2 (1 - q) ≤ 0 :=
    (Real.logb_nonpos_iff (by norm_num) (sub_pos.mpr hq1)).mpr (by linarith)
  have hterm : 0 ≤ -(1 - p) * Real.logb 2 (1 - q) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hcomp
  have hentropy := binaryEntropyBits_le_one p
  have _hentropy0 := binaryEntropyBits_nonneg hp0 hp1
  rw [binaryRelativeEntropy_eq_entropy, one_div, Real.logb_inv]
  nlinarith

/-- A useful global bound for handling nonpositive testing objectives. This
holds for the totalized scalar formula even at alternative endpoints. -/
theorem binaryRelativeEntropy_ge_neg_one {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    -1 ≤ binaryRelativeEntropy p q := by
  have hlogq : Real.logb 2 q ≤ 0 :=
    (Real.logb_nonpos_iff' (by norm_num) hq0).mpr hq1
  have hlogqc : Real.logb 2 (1 - q) ≤ 0 :=
    (Real.logb_nonpos_iff' (by norm_num) (by linarith)).mpr (by linarith)
  have hpterm : 0 ≤ -p * Real.logb 2 q :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hlogq
  have hcterm : 0 ≤ -(1 - p) * Real.logb 2 (1 - q) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hlogqc
  have hentropy := binaryEntropyBits_le_one p
  rw [binaryRelativeEntropy_eq_entropy]
  linarith

/-- A positive hockey-stick objective forces the alternative probability below
the reciprocal exponential threshold. -/
theorem positive_objective_q_lt_rpow_neg {p q x : ℝ} (hp1 : p ≤ 1)
    (hpositive : 0 < p - (2 : ℝ) ^ x * q) : q < (2 : ℝ) ^ (-x) := by
  have hpow : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  rw [Real.rpow_neg (by norm_num), ← one_div]
  apply (lt_div_iff₀ hpow).mpr
  nlinarith

/-- Explicit domination supplies the support condition at a zero alternative
acceptance probability. -/
theorem zero_of_domination {p q c : ℝ} (hp0 : 0 ≤ p) (hdom : p ≤ c * q) (hq : q = 0) :
    p = 0 := by
  rw [hq, mul_zero] at hdom
  exact le_antisymm hdom hp0

/-- Scalar hockey-stick estimate with an explicit zero-support hypothesis.
The nonpositive-objective branch is handled separately. -/
theorem hockeyStick_le_min_of_support {p q D x : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hx : 0 < x)
    (hD : binaryRelativeEntropy p q ≤ D) (hsupport : q = 0 → p = 0) :
    p - (2 : ℝ) ^ x * q ≤ min 1 ((D + 1) / x) := by
  have hweight : 0 ≤ (2 : ℝ) ^ x * q := by positivity
  have hle_p : p - (2 : ℝ) ^ x * q ≤ p := sub_le_self _ hweight
  have hDplus : 0 ≤ D + 1 := by
    have h := binaryRelativeEntropy_ge_neg_one hp0 hp1 hq0 hq1
    linarith
  refine le_min (hle_p.trans hp1) ?_
  by_cases hnonpos : p - (2 : ℝ) ^ x * q ≤ 0
  · exact hnonpos.trans (div_nonneg hDplus hx.le)
  have hpositive : 0 < p - (2 : ℝ) ^ x * q := lt_of_not_ge hnonpos
  have hqpos : 0 < q := by
    by_contra h
    have hzero : q = 0 := by linarith
    have hpzero := hsupport hzero
    simp [hzero, hpzero] at hpositive
  have hqsmall := positive_objective_q_lt_rpow_neg hp1 hpositive
  have hlog : Real.logb 2 q < -x :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) hqpos).mpr hqsmall
  have hqstrict : q < 1 :=
    (Real.logb_neg_iff (by norm_num : (1 : ℝ) < 2) hqpos).mp (by linarith)
  have hreciprocal : x ≤ Real.logb 2 (1 / q) := by
    rw [one_div, Real.logb_inv]
    linarith
  have hbound := (binaryRelativeEntropy_lower_bound hp0 hp1 hqpos hqstrict).trans hD
  have hpx : p * x ≤ D + 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hreciprocal hp0]
  exact hle_p.trans ((le_div_iff₀ hx).mpr hpx)

/-- The numerical estimate used in Lemma 4.3, with zero-support compatibility
derived from an actual scalar domination inequality `p ≤ c*q`. -/
theorem hockeyStick_le_min_of_domination {p q D x c : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hx : 0 < x)
    (hD : binaryRelativeEntropy p q ≤ D) (hdom : p ≤ c * q) :
    p - (2 : ℝ) ^ x * q ≤ min 1 ((D + 1) / x) :=
  hockeyStick_le_min_of_support hp0 hp1 hq0 hq1 hx hD (zero_of_domination hp0 hdom)

/-- A strict rate gap permits a fixed contraction margin above `sqrt(d/r)`. -/
theorem exists_constant_error_margin {d r : ℝ} (hd : 0 ≤ d) (hdr : d < r) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧ d / r < delta ^ 2 := by
  have hr : 0 < r := hd.trans_lt hdr
  have hratio : d / r < 1 := (div_lt_one hr).mpr hdr
  have hsqrt : Real.sqrt (d / r) < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hratio)
  obtain ⟨delta, hdelta, hdelta1⟩ := exists_between hsqrt
  have hdelta0 : 0 < delta := (Real.sqrt_nonneg _).trans_lt hdelta
  exact ⟨delta, hdelta0, hdelta1,
    (Real.sqrt_lt (div_nonneg hd hr.le) hdelta0.le).mp hdelta⟩

/-- The finite-block testing ratio is eventually below every strict margin
above its limiting rate ratio, proved from an explicit reciprocal threshold. -/
theorem eventually_testing_ratio_le {d r C : ℝ} (hr : 0 < r) (hgap : d / r < C) :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) * d + 1) / ((n : ℝ) * r) ≤ C := by
  have hg : 0 < C - d / r := sub_pos.mpr hgap
  obtain ⟨M, hM⟩ := exists_nat_ge (1 / (r * (C - d / r)))
  filter_upwards [eventually_ge_atTop M, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hlarge : 1 / (r * (C - d / r)) ≤ (n : ℝ) := hM.trans (by exact_mod_cast hn)
  have hbudget : 1 ≤ (n : ℝ) * (r * (C - d / r)) :=
    (div_le_iff₀ (mul_pos hr hg)).mp hlarge
  have hsmall : 1 / ((n : ℝ) * r) ≤ C - d / r :=
    (div_le_iff₀ (mul_pos hnpos hr)).mpr (by nlinarith)
  have heq : ((n : ℝ) * d + 1) / ((n : ℝ) * r) = d / r + 1 / ((n : ℝ) * r) := by
    field_simp
  rw [heq]
  linarith

/-- The scalar constant-error input used to start the paper's amplification
argument, after the genuine channel-testing bound has been established. -/
theorem exists_margin_eventually_testing_ratio_le {d r : ℝ} (hd : 0 ≤ d) (hdr : d < r) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      ∀ᶠ n : ℕ in atTop, ((n : ℝ) * d + 1) / ((n : ℝ) * r) ≤ delta ^ 2 := by
  obtain ⟨delta, hdelta0, hdelta1, hgap⟩ := exists_constant_error_margin hd hdr
  exact ⟨delta, hdelta0, hdelta1, eventually_testing_ratio_le (hd.trans_lt hdr) hgap⟩

end QuantumChannelStein.BinaryEntropyBounds
