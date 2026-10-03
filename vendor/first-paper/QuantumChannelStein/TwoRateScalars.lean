import QuantumChannelStein.ScalarBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar decay and rate iteration for two-rate amplification

These estimates implement the scalar parts of Lemma 4.4 of arXiv:2609.27196v1.
A Chernoff parameter replaces the entropy-binomial estimate: for a positive
retained-term bound `a` and a residual bound `0 ≤ b < 1`, suitable fixed
parameters make the weighted binomial tail exactly exponentially decaying.
The geometric rate iteration is proved separately from any operator or channel
construction. Its abstract induction lemma assumes only the explicit one-step
rate-improvement implication, rather than the conclusion of the iteration.
-/

noncomputable section
namespace QuantumChannelStein.TwoRateScalars
open Filter Topology

/-- The Chernoff weighted power is exactly a power of its one-block ratio. -/
theorem chernoff_weighted_power_eq {z : ℝ} (hz : 0 < z)
    (a b beta : ℝ) (m : ℕ) :
    z ^ (-(beta * (m : ℝ))) * (a + z * b) ^ m =
      ((a + z * b) / z ^ beta) ^ m := by
  rw [Real.rpow_neg hz.le, Real.rpow_mul hz.le, Real.rpow_natCast, div_pow]
  ring

/-- Any positive retained-term bound and residual bound strictly below one
admit a fixed Chernoff fraction strictly between zero and one. -/
theorem exists_chernoff_fraction {a b : ℝ} (ha : 0 < a)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    ∃ beta z : ℝ, 0 < beta ∧ beta < 1 ∧ 1 < z ∧ a + z * b < z ^ beta := by
  obtain ⟨z, hz⟩ := exists_gt (max 1 (a / (1 - b)))
  have hz1 : 1 < z := (le_max_left _ _).trans_lt hz
  have hz0 : 0 < z := zero_lt_one.trans hz1
  have hratio : a / (1 - b) < z := (le_max_right _ _).trans_lt hz
  have haz : a + z * b < z := by
    have := (div_lt_iff₀ (sub_pos.mpr hb1)).mp hratio
    nlinarith
  have habpos : 0 < a + z * b := add_pos_of_pos_of_nonneg ha (mul_nonneg hz0.le hb0)
  have hlog : Real.logb z (a + z * b) < 1 :=
    (Real.logb_lt_iff_lt_rpow hz1 habpos).mpr (by simpa using haz)
  obtain ⟨beta, hbeta, hbeta1⟩ := exists_between (max_lt (by norm_num : (0 : ℝ) < 1) hlog)
  refine ⟨beta, z, (le_max_left _ _).trans_lt hbeta, hbeta1, hz1, ?_⟩
  exact (Real.logb_lt_iff_lt_rpow hz1 habpos).mp ((le_max_right _ _).trans_lt hbeta)

/-- A Chernoff fraction with strict slack gives an explicit positive exponential
rate. The identity is valid at every natural block repetition count. -/
theorem chernoff_decay_of_fraction {a b beta z : ℝ}
    (hab : 0 < a + z * b) (hz : 0 < z) (hgap : a + z * b < z ^ beta) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ m : ℕ, z ^ (-(beta * (m : ℝ))) * (a + z * b) ^ m =
        Real.exp (-kappa * (m : ℝ)) := by
  let c := (a + z * b) / z ^ beta
  have hc0 : 0 < c := div_pos hab (Real.rpow_pos_of_pos hz beta)
  have hc1 : c < 1 := (div_lt_one (Real.rpow_pos_of_pos hz beta)).mpr hgap
  refine ⟨-Real.log c, neg_pos.mpr (Real.log_neg hc0 hc1), ?_⟩
  intro m
  rw [chernoff_weighted_power_eq hz]
  change c ^ m = Real.exp (-(-Real.log c) * (m : ℝ))
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hc0]
  simp

/-- Fixed positive Chernoff decay parameters exist whenever the residual norm
bound is strictly smaller than one. -/
theorem exists_chernoff_decay {a b : ℝ} (ha : 0 < a)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    ∃ beta z kappa : ℝ, 0 < beta ∧ beta < 1 ∧ 1 < z ∧ 0 < kappa ∧
      a + z * b < z ^ beta ∧
      ∀ m : ℕ, z ^ (-(beta * (m : ℝ))) * (a + z * b) ^ m =
        Real.exp (-kappa * (m : ℝ)) := by
  obtain ⟨beta, z, hbeta0, hbeta1, hz, hgap⟩ := exists_chernoff_fraction ha hb0 hb1
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hab : 0 < a + z * b := add_pos_of_pos_of_nonneg ha (mul_nonneg hz0.le hb0)
  obtain ⟨kappa, hkappa, hdecay⟩ := chernoff_decay_of_fraction hab hz0 hgap
  exact ⟨beta, z, kappa, hbeta0, hbeta1, hz, hkappa, hgap, hdecay⟩

/-- Parameters for the actual retained and residual bounds in Lemma 4.4,
`a = 1 + delta` and `b = (1 + delta) / 2`. -/
theorem exists_two_rate_tail_parameters {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1) :
    ∃ beta z kappa : ℝ, 0 < beta ∧ beta < 1 ∧ 1 < z ∧ 0 < kappa ∧
      (1 + delta) + z * ((1 + delta) / 2) < z ^ beta ∧
      ∀ m : ℕ, z ^ (-(beta * (m : ℝ))) *
          ((1 + delta) + z * ((1 + delta) / 2)) ^ m =
        Real.exp (-kappa * (m : ℝ)) :=
  exists_chernoff_decay (by linarith) (by linarith) (by linarith)

/-- The explicit contraction parameter used in the paper is between the
truncation fraction and one. -/
theorem midpoint_contraction {beta : ℝ} (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    beta < (1 + beta) / 2 ∧ 0 < (1 + beta) / 2 ∧ (1 + beta) / 2 < 1 := by
  constructor
  · linarith
  constructor <;> linarith

/-- Geometrically interpolated cost rates. -/
def iteratedRate (r L theta : ℝ) (j : ℕ) : ℝ := r + theta ^ j * (L - r)

@[simp] theorem iteratedRate_zero (r L theta : ℝ) : iteratedRate r L theta 0 = L := by
  simp [iteratedRate]

/-- Every finite iterated rate remains above the low rate. -/
theorem low_lt_iteratedRate {r L theta : ℝ} (hrL : r < L) (htheta : 0 < theta)
    (j : ℕ) : r < iteratedRate r L theta j := by
  have h := mul_pos (pow_pos htheta j) (sub_pos.mpr hrL)
  dsimp [iteratedRate]
  linarith

/-- Exact slack between successive iterated rates and the required convex
combination of the preceding rate. -/
theorem iteratedRate_step_gap (r L beta theta : ℝ) (j : ℕ) :
    iteratedRate r L theta (j + 1) -
        ((1 - beta) * r + beta * iteratedRate r L theta j) =
      (theta - beta) * theta ^ j * (L - r) := by
  simp only [iteratedRate, pow_succ]
  ring

/-- Each iteration satisfies the strict cost-interpolation condition. -/
theorem interpolation_lt_next_rate {r L beta theta : ℝ}
    (hrL : r < L) (htheta : 0 < theta) (hbeta : beta < theta) (j : ℕ) :
    (1 - beta) * r + beta * iteratedRate r L theta j <
      iteratedRate r L theta (j + 1) := by
  have hpos := mul_pos (mul_pos (sub_pos.mpr hbeta) (pow_pos htheta j)) (sub_pos.mpr hrL)
  rw [← iteratedRate_step_gap r L beta theta j] at hpos
  linarith

/-- The iterated rates converge to the low rate. -/
theorem tendsto_iteratedRate {r L theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) :
    Tendsto (iteratedRate r L theta) atTop (𝓝 r) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one htheta0 htheta1).mul_const (L - r)
  simpa [iteratedRate] using h.const_add r

/-- Every strict target above the low rate is reached after finitely many steps. -/
theorem eventually_iteratedRate_lt {r L theta R : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (hR : r < R) :
    ∀ᶠ j : ℕ in atTop, iteratedRate r L theta j < R :=
  (tendsto_iteratedRate htheta0 htheta1).eventually_lt_const hR

/-- A concrete one-step improvement theorem can be iterated without choosing an
infinite sequence of auxiliary maps. The output uses a finite iteration count. -/
theorem exists_improved_rate {P : ℝ → Prop} {r L R beta : ℝ}
    (hrL : r < L) (hR : r < R) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hstart : P L)
    (hstep : ∀ S S' : ℝ, r < S → (1 - beta) * r + beta * S < S' → P S → P S') :
    ∃ j : ℕ, iteratedRate r L ((1 + beta) / 2) j < R ∧
      P (iteratedRate r L ((1 + beta) / 2) j) := by
  obtain ⟨hbetatheta, htheta0, htheta1⟩ := midpoint_contraction hbeta0 hbeta1
  have hP : ∀ j : ℕ, P (iteratedRate r L ((1 + beta) / 2) j) := by
    intro j
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
      exact hstep _ _ (low_lt_iteratedRate hrL htheta0 j)
        (interpolation_lt_next_rate hrL htheta0 hbetatheta j) ih
  obtain ⟨j, hj⟩ := (eventually_iteratedRate_lt (L := L) htheta0.le htheta1 hR).exists
  exact ⟨j, hj, hP j⟩

/-- Every finite number of halvings leaves a strictly positive error exponent. -/
theorem iterated_error_exponent_pos (j : ℕ) : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity

/-- A polynomial prefactor is absorbed by halving a positive stretched-
exponential rate. The statement allows any real polynomial exponent. -/
theorem eventually_rpow_mul_stretched_exp_le {a gamma : ℝ}
    (ha : 0 < a) (hgamma : 0 < gamma) (p : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      x ^ p * Real.exp (-gamma * x ^ a) ≤ Real.exp (-(gamma / 2) * x ^ a) := by
  have hsmall := ((isLittleO_log_rpow_atTop ha).const_mul_left p).bound
    (show 0 < gamma / 2 by positivity)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hlog : p * Real.log x ≤ gamma / 2 * x ^ a := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_pos_of_pos hx0 a).le]
      using (le_abs_self (p * Real.log x)).trans hx
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A positive stretched exponential tends to zero. -/
theorem tendsto_stretched_exp_zero {a gamma : ℝ} (ha : 0 < a) (hgamma : 0 < gamma) :
    Tendsto (fun x : ℝ => Real.exp (-gamma * x ^ a)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, Real.rpow_zero, one_mul] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 gamma hgamma).comp
    (tendsto_rpow_atTop ha)

/-- Polynomial times stretched exponential tends to zero, with an arbitrary
fixed real prefactor. -/
theorem tendsto_scaled_rpow_stretched_exp_zero {a gamma : ℝ}
    (ha : 0 < a) (hgamma : 0 < gamma) (C p : ℝ) :
    Tendsto (fun x : ℝ => C * (x ^ p * Real.exp (-gamma * x ^ a))) atTop (𝓝 0) := by
  have hzero : Tendsto (fun x : ℝ => x ^ p * Real.exp (-gamma * x ^ a)) atTop (𝓝 0) := by
    apply squeeze_zero' _ (eventually_rpow_mul_stretched_exp_le ha hgamma p)
      (tendsto_stretched_exp_zero ha (show 0 < gamma / 2 by positivity))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx _) (Real.exp_pos _).le
  simpa using hzero.const_mul C

/-- The integer square root tends to infinity without passing to an assumed
real-valued asymptotic equivalence. -/
theorem tendsto_nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (b * b)] with N hN
  exact Nat.le_sqrt.mpr hN

/-- Exact comparisons between the integer square-root block size and the
number of complete blocks. -/
theorem sqrt_block_nat_bounds (N : ℕ) (hN : 0 < N) :
    0 < Nat.sqrt N ∧ Nat.sqrt N ≤ N / Nat.sqrt N ∧
      N / Nat.sqrt N ≤ 3 * Nat.sqrt N := by
  have hn : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr hN
  have hm : Nat.sqrt N ≤ N / Nat.sqrt N :=
    (Nat.le_div_iff_mul_le hn).mpr (Nat.sqrt_le N)
  have hmprod := Nat.div_mul_le_self N (Nat.sqrt N)
  have hNbound := Nat.sqrt_le_add N
  refine ⟨hn, hm, ?_⟩
  nlinarith

/-- Both the integer block size and the repetition count are controlled by
fixed multiples of the real square root, uniformly for positive blocklengths. -/
theorem sqrt_block_real_bounds (N : ℕ) (hN : 0 < N) :
    Real.sqrt (N : ℝ) / 2 ≤ (Nat.sqrt N : ℝ) ∧
      (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) ∧
      Real.sqrt (N : ℝ) / 2 ≤ (N / Nat.sqrt N : ℕ) ∧
      ((N / Nat.sqrt N : ℕ) : ℝ) ≤ 3 * Real.sqrt (N : ℝ) := by
  obtain ⟨hn, hnm, hm⟩ := sqrt_block_nat_bounds N hN
  have hn1 : (1 : ℝ) ≤ Nat.sqrt N := by exact_mod_cast hn
  have hround : Real.sqrt (N : ℝ) < (Nat.sqrt N : ℝ) + 1 :=
    Real.real_sqrt_lt_nat_sqrt_succ
  have hlow : Real.sqrt (N : ℝ) / 2 ≤ (Nat.sqrt N : ℝ) := by linarith
  have hupp : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hnmR : (Nat.sqrt N : ℝ) ≤ (N / Nat.sqrt N : ℕ) := by exact_mod_cast hnm
  have hmR : ((N / Nat.sqrt N : ℕ) : ℝ) ≤ 3 * (Nat.sqrt N : ℝ) := by exact_mod_cast hm
  exact ⟨hlow, hupp, hlow.trans hnmR, hmR.trans (by linarith)⟩

/-- Integer square-root blocking halves a positive stretched exponent, with
an explicit constant loss of `(1/2)^a`. -/
theorem sqrt_block_rpow_lower (N : ℕ) (hN : 0 < N) {a : ℝ} (ha : 0 ≤ a) :
    (1 / 2 : ℝ) ^ a * (N : ℝ) ^ (a / 2) ≤ (Nat.sqrt N : ℝ) ^ a := by
  have hlow := (sqrt_block_real_bounds N hN).1
  calc
    (1 / 2 : ℝ) ^ a * (N : ℝ) ^ (a / 2) =
        ((1 / 2 : ℝ) * Real.sqrt (N : ℝ)) ^ a := by
      rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 2
      ring
    _ ≤ (Nat.sqrt N : ℝ) ^ a :=
      Real.rpow_le_rpow (by positivity) (by linarith) ha

/-- The telescoping repetition factor stays below two whenever the accumulated
one-block error is at most `log 2`. -/
theorem repetition_factor_le_two (m : ℕ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hsmall : (m : ℝ) * epsilon ≤ Real.log 2) :
    (1 + epsilon) ^ (m - 1) ≤ (2 : ℝ) := by
  have hbase : 1 + epsilon ≤ Real.exp epsilon := by linarith [Real.add_one_le_exp epsilon]
  calc
    (1 + epsilon) ^ (m - 1) ≤ (Real.exp epsilon) ^ (m - 1) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp ((m - 1 : ℕ) * epsilon) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((m : ℝ) * epsilon) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le m 1) hepsilon
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hsmall
    _ = 2 := Real.exp_log (by norm_num)

/-- The accumulated envelope error for integer square-root blocking is bounded
by a square-root prefactor times a stretched exponential. -/
theorem sqrt_accumulated_error_le (N : ℕ) (hN : 0 < N)
    {K gamma a : ℝ} (hK : 0 ≤ K) (hgamma : 0 ≤ gamma) (ha : 0 ≤ a) :
    (N / Nat.sqrt N : ℕ) * (K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a)) ≤
      3 * K * (Real.sqrt (N : ℝ) *
        Real.exp (-(gamma * (1 / 2 : ℝ) ^ a) * (N : ℝ) ^ (a / 2))) := by
  have hm := (sqrt_block_real_bounds N hN).2.2.2
  have hp := sqrt_block_rpow_lower N hN ha
  have hexp : Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a) ≤
      Real.exp (-(gamma * (1 / 2 : ℝ) ^ a) * (N : ℝ) ^ (a / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hp hgamma]
  calc
    (N / Nat.sqrt N : ℕ) * (K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a)) ≤
        (3 * Real.sqrt (N : ℝ)) * (K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a)) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ ≤ (3 * Real.sqrt (N : ℝ)) * (K *
        Real.exp (-(gamma * (1 / 2 : ℝ) ^ a) * (N : ℝ) ^ (a / 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hK) (by positivity)
    _ = _ := by ring

/-- The accumulated envelope error is eventually at most `log 2`, so the
repetition factor does not spoil stretched-exponential decay. -/
theorem eventually_sqrt_accumulated_error_small {K gamma a : ℝ}
    (hK : 0 ≤ K) (hgamma : 0 < gamma) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop,
      (N / Nat.sqrt N : ℕ) * (K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a)) ≤
        Real.log 2 := by
  have hc : 0 < gamma * (1 / 2 : ℝ) ^ a := by positivity
  have hlim := (tendsto_scaled_rpow_stretched_exp_zero
    (show 0 < a / 2 by positivity) hc (3 * K) (1 / 2)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hsmall := hlim.eventually_le_const (show (0 : ℝ) < Real.log 2 from Real.log_pos (by norm_num))
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with N hN hN0
  apply (sqrt_accumulated_error_le N hN0 hK hgamma.le ha.le).trans
  simpa only [Function.comp_def, ← Real.sqrt_eq_rpow] using hN

/-- Halving the stretched decay constant absorbs the square-root prefactor in
the accumulated envelope error. -/
theorem eventually_sqrt_accumulated_error_exp {K gamma a : ℝ}
    (hK : 0 ≤ K) (hgamma : 0 < gamma) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop,
      (N / Nat.sqrt N : ℕ) * (K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a)) ≤
        3 * K * Real.exp (-((gamma * (1 / 2 : ℝ) ^ a) / 2) * (N : ℝ) ^ (a / 2)) := by
  have hc : 0 < gamma * (1 / 2 : ℝ) ^ a := by positivity
  have hpoly :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (eventually_rpow_mul_stretched_exp_le (show 0 < a / 2 by positivity) hc (1 / 2))
  filter_upwards [hpoly, eventually_gt_atTop (0 : ℕ)] with N hN hN0
  apply (sqrt_accumulated_error_le N hN0 hK hgamma.le ha.le).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [← Real.sqrt_eq_rpow] using hN

/-- The Chernoff decay in the number of repetitions controls the desired
halved stretched exponent at every positive external blocklength. -/
theorem sqrt_chernoff_error_le (N : ℕ) (hN : 0 < N)
    {kappa a : ℝ} (hkappa : 0 ≤ kappa) (ha1 : a ≤ 1) :
    Real.exp (-kappa * (N / Nat.sqrt N : ℕ)) ≤
      Real.exp (-(kappa / 2) * (N : ℝ) ^ (a / 2)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (N : ℝ) ^ (a / 2) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hm := (sqrt_block_real_bounds N hN).2.2.1
  apply Real.exp_le_exp.mpr
  have hlower : (N : ℝ) ^ (a / 2) / 2 ≤ (N / Nat.sqrt N : ℕ) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hlower hkappa]

/-- The full two-rate truncation plus telescoping error after integer
square-root blocking is stretched-exponentially small. This supplies the
actual scalar estimate in Step 3 of Lemma 4.4. -/
theorem sqrt_block_total_error_bound {K gamma kappa a : ℝ}
    (hK : 0 < K) (hgamma : 0 < gamma) (hkappa : 0 < kappa)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ K' gamma' : ℝ, 0 < K' ∧ 0 < gamma' ∧
      ∀ᶠ N : ℕ in atTop,
        Real.exp (-kappa * (N / Nat.sqrt N : ℕ)) +
          ((N / Nat.sqrt N : ℕ) * (K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a))) *
            (1 + K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a)) ^ (N / Nat.sqrt N - 1) ≤
          K' * Real.exp (-gamma' * (N : ℝ) ^ (a / 2)) := by
  let c := gamma * (1 / 2 : ℝ) ^ a / 2
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨1 + 6 * K, min (kappa / 2) c, by positivity,
    lt_min (by positivity) hc, ?_⟩
  filter_upwards [eventually_sqrt_accumulated_error_small hK.le hgamma ha,
    eventually_sqrt_accumulated_error_exp hK.le hgamma ha,
    eventually_gt_atTop (0 : ℕ)] with N hsmall hdecay hN
  have he : 0 ≤ K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a) := by positivity
  have hfactor := repetition_factor_le_two (N / Nat.sqrt N) he hsmall
  have htel :
      ((N / Nat.sqrt N : ℕ) * (K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a))) *
          (1 + K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a)) ^ (N / Nat.sqrt N - 1) ≤
        6 * K * Real.exp (-c * (N : ℝ) ^ (a / 2)) := by
    calc
      _ ≤ ((N / Nat.sqrt N : ℕ) * (K * Real.exp (-gamma * (Nat.sqrt N : ℝ) ^ a))) * 2 :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ (3 * K * Real.exp (-c * (N : ℝ) ^ (a / 2))) * 2 :=
        mul_le_mul_of_nonneg_right hdecay (by norm_num)
      _ = _ := by ring
  exact (add_le_add (sqrt_chernoff_error_le N hN hkappa.le ha1) htel).trans
    (ScalarBounds.exp_sum_le (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by positivity))

/-- The stretched-exponential error envelope vanishes along natural
blocklengths. The prefactor may be any fixed real number. -/
theorem stretched_error_tendsto_zero (K : ℝ) {gamma alpha : ℝ}
    (hgamma : 0 < gamma) (halpha : 0 < alpha) :
    Tendsto (fun n : ℕ => K * Real.exp (-gamma * (n : ℝ) ^ alpha)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, mul_zero] using
    ((tendsto_stretched_exp_zero halpha hgamma).const_mul K).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

/-- The retained counting cost and exact-padding cost as one base-two power. -/
theorem retained_padding_cost_eq (n m ell : ℕ) (Sbar L : ℝ) :
    ((3 : ℝ) ^ m * (2 : ℝ) ^ ((n : ℝ) * m * Sbar / 2)) *
        (2 : ℝ) ^ ((ell : ℝ) * L / 2) =
      (2 : ℝ) ^ (((n : ℝ) * m * Sbar + (ell : ℝ) * L + 2 * m * Real.logb 2 3) / 2) := by
  have hthree : (3 : ℝ) ^ m = (2 : ℝ) ^ (Real.logb 2 3 * (m : ℝ)) := by
    rw [Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]
  rw [hthree, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  ring

/-- The excess numerator of the square-root-blocking cost is eventually
absorbed by every strict target-rate gap. -/
theorem eventually_sqrt_cost_exponent_le {Sbar R L : ℝ} (hgap : Sbar < R) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.sqrt N : ℝ) * (N / Nat.sqrt N : ℕ) * Sbar +
          (N % Nat.sqrt N : ℕ) * L + 2 * (N / Nat.sqrt N : ℕ) * Real.logb 2 3 ≤
        (N : ℝ) * R := by
  let C := |L - Sbar| + 6 * |Real.logb 2 3|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsqrt : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
      tendsto_nat_sqrt_atTop
  filter_upwards [hsqrt.eventually_ge_atTop (C / (R - Sbar)),
    eventually_gt_atTop (0 : ℕ)] with N hlarge hN
  have hn : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr hN
  have hdecomp : (Nat.sqrt N : ℝ) * (N / Nat.sqrt N : ℕ) +
      (N % Nat.sqrt N : ℕ) = (N : ℝ) := by
    exact_mod_cast Nat.div_add_mod N (Nat.sqrt N)
  have hrem : ((N % Nat.sqrt N : ℕ) : ℝ) ≤ (Nat.sqrt N : ℝ) := by
    exact_mod_cast (Nat.mod_lt N hn).le
  have hrem0 : (0 : ℝ) ≤ (N % Nat.sqrt N : ℕ) := Nat.cast_nonneg _
  have hm : ((N / Nat.sqrt N : ℕ) : ℝ) ≤ 3 * (Nat.sqrt N : ℝ) := by
    exact_mod_cast (sqrt_block_nat_bounds N hN).2.2
  have hn2 : (Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le N
  have htail : (N % Nat.sqrt N : ℕ) * (L - Sbar) ≤ (Nat.sqrt N : ℝ) * |L - Sbar| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hrem0).trans
      (mul_le_mul_of_nonneg_right hrem (abs_nonneg _))
  have hcount : 2 * (N / Nat.sqrt N : ℕ) * Real.logb 2 3 ≤
      6 * (Nat.sqrt N : ℝ) * |Real.logb 2 3| := by
    calc
      _ ≤ 2 * (N / Nat.sqrt N : ℕ) * |Real.logb 2 3| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ (2 * (3 * (Nat.sqrt N : ℝ))) * |Real.logb 2 3| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) (abs_nonneg _)
      _ = _ := by ring
  have hbudget : (Nat.sqrt N : ℝ) * C ≤ (N : ℝ) * (R - Sbar) := by
    have hbase : C ≤ (Nat.sqrt N : ℝ) * (R - Sbar) :=
      (div_le_iff₀ (sub_pos.mpr hgap)).mp hlarge
    calc
      _ ≤ (Nat.sqrt N : ℝ) * ((Nat.sqrt N : ℝ) * (R - Sbar)) :=
        mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg _)
      _ = ((Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ)) * (R - Sbar) := by ring
      _ ≤ (N : ℝ) * (R - Sbar) := mul_le_mul_of_nonneg_right hn2 (sub_pos.mpr hgap).le
  calc
    _ = (N : ℝ) * Sbar + (N % Nat.sqrt N : ℕ) * (L - Sbar) +
        2 * (N / Nat.sqrt N : ℕ) * Real.logb 2 3 := by rw [← hdecomp]; ring
    _ ≤ (N : ℝ) * Sbar + (Nat.sqrt N : ℝ) * |L - Sbar| +
        6 * (Nat.sqrt N : ℝ) * |Real.logb 2 3| :=
      add_le_add (add_le_add le_rfl htail) hcount
    _ = (N : ℝ) * Sbar + (Nat.sqrt N : ℝ) * C := by dsimp [C]; ring
    _ ≤ (N : ℝ) * Sbar + (N : ℝ) * (R - Sbar) := add_le_add le_rfl hbudget
    _ = (N : ℝ) * R := by ring

/-- Retained auxiliary cost with exact remainder padding satisfies every strict
rate target above the interpolated rate for all sufficiently large blocklengths. -/
theorem eventually_sqrt_padded_cost_le {Sbar R L : ℝ} (hgap : Sbar < R) :
    ∀ᶠ N : ℕ in atTop,
      ((3 : ℝ) ^ (N / Nat.sqrt N) *
          (2 : ℝ) ^ ((Nat.sqrt N : ℝ) * (N / Nat.sqrt N : ℕ) * Sbar / 2)) *
          (2 : ℝ) ^ ((N % Nat.sqrt N : ℕ) * L / 2) ≤ (2 : ℝ) ^ ((N : ℝ) * R / 2) := by
  filter_upwards [eventually_sqrt_cost_exponent_le (L := L) hgap] with N hN
  rw [retained_padding_cost_eq]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (div_le_div_of_nonneg_right hN (by norm_num))

end QuantumChannelStein.TwoRateScalars
