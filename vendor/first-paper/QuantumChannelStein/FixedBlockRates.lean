import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar rate selection and padding for fixed-block amplification

These real-variable and natural-number estimates implement the arithmetic in
Lemma 4.5 of arXiv:2609.27196v1. They select a fixed accurate block from genuine
convergence, rewrite the retained-term cost, and control the actual quotient
and remainder of each external blocklength. They do not assert a quantum
approximation theorem or assume its asymptotic conclusion.
-/

noncomputable section
namespace QuantumChannelStein.FixedBlockRates
open Filter Topology

/-- A strict pair of rate gaps permits a mixing fraction strictly between zero
and one, whose interpolated rate is still below the target. -/
theorem exists_mixing_fraction {S R L : ℝ} (hSR : S < R) (hRL : R < L) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ S + eta * (L - S) < R := by
  have hLS : 0 < L - S := by linarith
  have hratio : 0 < (R - S) / (L - S) := div_pos (sub_pos.mpr hSR) hLS
  obtain ⟨eta, heta, hupper⟩ := exists_between hratio
  have hratio1 : (R - S) / (L - S) < 1 :=
    (div_lt_one hLS).mpr (by linarith)
  refine ⟨eta, heta, hupper.trans hratio1, ?_⟩
  have := (lt_div_iff₀ hLS).mp hupper
  linarith

/-- Any eventual property can be imposed on an arbitrarily late positive
block while making the base-three counting correction smaller than a strict
rate gap. This version accepts an eventual approximation-existence property
directly, without choosing a sequence of auxiliary maps or errors. -/
theorem choose_large_block {P : ℕ → Prop} {Rbar R : ℝ}
    (hP : ∀ᶠ l in atTop, P l) (hgap : Rbar < R) (minBlock : ℕ) :
    ∃ l : ℕ, minBlock ≤ l ∧ 0 < l ∧ P l ∧
      Rbar + 2 * Real.logb 2 3 / (l : ℝ) < R := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hP
  obtain ⟨M, hM⟩ := exists_nat_gt (max 0 (2 * Real.logb 2 3 / (R - Rbar)))
  let l := max N (max minBlock M)
  have hNl : N ≤ l := le_max_left _ _
  have hminl : minBlock ≤ l := (le_max_left _ _).trans (le_max_right _ _)
  have hMl : M ≤ l := (le_max_right _ _).trans (le_max_right _ _)
  have hMpos : (0 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hlpos : (0 : ℝ) < l := hMpos.trans_le (by exact_mod_cast hMl)
  have hlarge : 2 * Real.logb 2 3 / (R - Rbar) < (l : ℝ) :=
    ((le_max_right _ _).trans_lt hM).trans_le (by exact_mod_cast hMl)
  have hmul : 2 * Real.logb 2 3 < (l : ℝ) * (R - Rbar) :=
    (div_lt_iff₀ (sub_pos.mpr hgap)).mp hlarge
  have hdiv : 2 * Real.logb 2 3 / (l : ℝ) < R - Rbar :=
    (div_lt_iff₀ hlpos).mpr (by nlinarith)
  exact ⟨l, hminl, by exact_mod_cast hlpos, hN l hNl, by linarith⟩

/-- Vanishing error supplies an arbitrarily late positive fixed block satisfying
both the truncation-error threshold and the strict adjusted-rate bound. -/
theorem exists_accurate_block {epsilon : ℕ → ℝ} {Rbar R eta : ℝ}
    (hepsilon : Tendsto epsilon atTop (𝓝 0)) (hgap : Rbar < R)
    (minBlock : ℕ) :
    ∃ l : ℕ, minBlock ≤ l ∧ 0 < l ∧
      epsilon l ≤ 1 / (1 + (4 : ℝ) ^ (1 / eta)) ∧
      Rbar + 2 * Real.logb 2 3 / (l : ℝ) < R := by
  have hthreshold : (0 : ℝ) < 1 / (1 + (4 : ℝ) ^ (1 / eta)) := by positivity
  have hevent : ∀ᶠ n in atTop, epsilon n ≤ 1 / (1 + (4 : ℝ) ^ (1 / eta)) :=
    hepsilon.eventually_le_const hthreshold
  exact choose_large_block hevent hgap minBlock

/-- Simultaneous choice of the mixing fraction and an arbitrarily late
accurate fixed block from a vanishing-error sequence. -/
theorem exists_fixed_block_parameters {epsilon : ℕ → ℝ} {S R L : ℝ}
    (hepsilon : Tendsto epsilon atTop (𝓝 0)) (hSR : S < R) (hRL : R < L)
    (minBlock : ℕ) :
    ∃ (eta : ℝ) (l : ℕ), 0 < eta ∧ eta < 1 ∧ minBlock ≤ l ∧ 0 < l ∧
      epsilon l ≤ 1 / (1 + (4 : ℝ) ^ (1 / eta)) ∧
      S + eta * (L - S) + 2 * Real.logb 2 3 / (l : ℝ) < R := by
  obtain ⟨eta, heta0, heta1, hrate⟩ := exists_mixing_fraction hSR hRL
  obtain ⟨l, hlmin, hl, he, hv⟩ := exists_accurate_block (eta := eta) hepsilon hrate minBlock
  exact ⟨eta, l, heta0, heta1, hlmin, hl, he, hv⟩

/-- The base-three counting factor becomes the additive rate correction
`2 log₂(3) / l`. Padding may already be present in the exponent. -/
theorem retained_cost_eq_adjusted_rate (l m r : ℕ) (hl : 0 < l) (Rbar L : ℝ) :
    (3 : ℝ) ^ m * (2 : ℝ) ^ ((l : ℝ) * m * Rbar / 2 + (r : ℝ) * L / 2) =
      (2 : ℝ) ^ ((l : ℝ) * m * (Rbar + 2 * Real.logb 2 3 / l) / 2 +
        (r : ℝ) * L / 2) := by
  have hthree : (3 : ℝ) ^ m = (2 : ℝ) ^ (Real.logb 2 3 * (m : ℝ)) := by
    rw [Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]
  rw [hthree, ← Real.rpow_add (by norm_num)]
  congr 1
  have hlzero : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  field_simp
  ring

/-- Quotient and remainder identity, cast to the rate's scalar field. -/
theorem cast_div_add_mod (N l : ℕ) :
    (l : ℝ) * (N / l : ℕ) + (N % l : ℕ) = (N : ℝ) := by
  exact_mod_cast Nat.div_add_mod N l

/-- An explicit finite threshold absorbs the exact bounded remainder. No sign
assumption on `L - v` is needed. -/
theorem padding_exponent_le (N l : ℕ) (hl : 0 < l) {v R L : ℝ} (hgap : v < R)
    (hN : (l : ℝ) * |L - v| / (R - v) ≤ (N : ℝ)) :
    (l : ℝ) * (N / l : ℕ) * v + (N % l : ℕ) * L ≤ (N : ℝ) * R := by
  have hdecomp := cast_div_add_mod N l
  have hrem : (N % l : ℝ) ≤ (l : ℝ) := by
    exact_mod_cast (Nat.mod_lt N hl).le
  have hrem0 : (0 : ℝ) ≤ (N % l : ℕ) := Nat.cast_nonneg _
  have htail : (N % l : ℝ) * (L - v) ≤ (l : ℝ) * |L - v| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hrem0).trans
      (mul_le_mul_of_nonneg_right hrem (abs_nonneg _))
  have hbudget : (l : ℝ) * |L - v| ≤ (N : ℝ) * (R - v) :=
    (div_le_iff₀ (sub_pos.mpr hgap)).mp hN
  calc
    (l : ℝ) * (N / l : ℕ) * v + (N % l : ℕ) * L =
        (N : ℝ) * v + (N % l : ℕ) * (L - v) := by
      rw [← hdecomp]
      ring
    _ ≤ (N : ℝ) * v + (l : ℝ) * |L - v| := add_le_add le_rfl htail
    _ ≤ (N : ℝ) * v + (N : ℝ) * (R - v) := add_le_add le_rfl hbudget
    _ = (N : ℝ) * R := by ring

/-- The remainder absorption applies to all sufficiently large external
blocklengths, with actual natural division and remainder. -/
theorem eventually_padding_exponent_le (l : ℕ) (hl : 0 < l)
    {v R L : ℝ} (hgap : v < R) :
    ∀ᶠ N : ℕ in atTop,
      (l : ℝ) * (N / l : ℕ) * v + (N % l : ℕ) * L ≤ (N : ℝ) * R := by
  obtain ⟨M, hM⟩ := exists_nat_ge ((l : ℝ) * |L - v| / (R - v))
  filter_upwards [eventually_ge_atTop M] with N hN
  apply padding_exponent_le N l hl hgap
  exact hM.trans (by exact_mod_cast hN)

/-- The complete scalar retained-cost estimate after exact padding. -/
theorem eventually_padded_retained_cost_le (l : ℕ) (hl : 0 < l)
    {Rbar R L : ℝ} (hgap : Rbar + 2 * Real.logb 2 3 / (l : ℝ) < R) :
    ∀ᶠ N : ℕ in atTop,
      (3 : ℝ) ^ (N / l) *
          (2 : ℝ) ^ ((l : ℝ) * (N / l : ℕ) * Rbar / 2 + (N % l : ℕ) * L / 2) ≤
        (2 : ℝ) ^ ((N : ℝ) * R / 2) := by
  filter_upwards [eventually_padding_exponent_le l hl (L := L) hgap] with N hN
  rw [retained_cost_eq_adjusted_rate l (N / l) (N % l) hl Rbar L]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

/-- Multiplicative form of the padded retained-cost bound, convenient for a
tensor-product operator-norm estimate. -/
theorem eventually_padded_retained_cost_mul_le (l : ℕ) (hl : 0 < l)
    {Rbar R L : ℝ} (hgap : Rbar + 2 * Real.logb 2 3 / (l : ℝ) < R) :
    ∀ᶠ N : ℕ in atTop,
      ((3 : ℝ) ^ (N / l) * (2 : ℝ) ^ ((l : ℝ) * (N / l : ℕ) * Rbar / 2)) *
          (2 : ℝ) ^ ((N % l : ℕ) * L / 2) ≤ (2 : ℝ) ^ ((N : ℝ) * R / 2) := by
  filter_upwards [eventually_padded_retained_cost_le l hl (L := L) hgap] with N hN
  simpa only [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] using hN

/-- The floor-block error is uniformly exponentially small at every external
blocklength, with prefactor two and decay rate `(log 2) / l`. -/
theorem half_pow_div_le_exponential (N l : ℕ) (hl : 0 < l) :
    (1 / 2 : ℝ) ^ (N / l) ≤
      2 * Real.exp (-(Real.log 2 / (l : ℝ)) * (N : ℝ)) := by
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdecomp := cast_div_add_mod N l
  have hrem : (N % l : ℝ) < (l : ℝ) := by exact_mod_cast Nat.mod_lt N hl
  have hres : 0 ≤ Real.log 2 / (l : ℝ) * ((l : ℝ) - (N % l : ℕ)) :=
    mul_nonneg (div_pos hlog hlpos).le (by linarith)
  have hexp : -Real.log 2 * (N / l : ℕ) ≤
      Real.log 2 - Real.log 2 / (l : ℝ) * (N : ℝ) := by
    have hid : Real.log 2 - Real.log 2 / (l : ℝ) * (N : ℝ) +
        Real.log 2 * (N / l : ℕ) =
        Real.log 2 / (l : ℝ) * ((l : ℝ) - (N % l : ℕ)) := by
      rw [← hdecomp]
      field_simp
      ring
    linarith
  calc
    (1 / 2 : ℝ) ^ (N / l) = Real.exp (-Real.log 2 * (N / l : ℕ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
      simp
    _ ≤ Real.exp (Real.log 2 - Real.log 2 / (l : ℝ) * (N : ℝ)) :=
      Real.exp_le_exp.mpr hexp
    _ = 2 * Real.exp (-(Real.log 2 / (l : ℝ)) * (N : ℝ)) := by
      rw [show Real.log 2 - Real.log 2 / (l : ℝ) * (N : ℝ) =
        Real.log 2 + (-(Real.log 2 / (l : ℝ)) * (N : ℝ)) by ring,
        Real.exp_add, Real.exp_log (by norm_num)]

/-- The decay rate chosen by fixed-block padding is positive. -/
theorem fixed_block_decay_rate_pos (l : ℕ) (hl : 0 < l) :
    0 < Real.log 2 / (l : ℝ) :=
  div_pos (Real.log_pos (by norm_num)) (by exact_mod_cast hl)

/-- The full scalar parameter package for Lemma 4.5: an accurate fixed block,
a positive exponential decay rate, and simultaneous eventual bounds on the
retained cost after padding and the floor-block error. -/
theorem exists_fixed_block_scalar_bounds {epsilon : ℕ → ℝ} {S R L : ℝ}
    (hepsilon : Tendsto epsilon atTop (𝓝 0)) (hSR : S < R) (hRL : R < L)
    (minBlock : ℕ) :
    ∃ (eta : ℝ) (l : ℕ) (gamma : ℝ),
      0 < eta ∧ eta < 1 ∧ minBlock ≤ l ∧ 0 < l ∧
      epsilon l ≤ 1 / (1 + (4 : ℝ) ^ (1 / eta)) ∧
      S + eta * (L - S) + 2 * Real.logb 2 3 / (l : ℝ) < R ∧
      0 < gamma ∧
      ∀ᶠ N : ℕ in atTop,
        (((3 : ℝ) ^ (N / l) *
              (2 : ℝ) ^ ((l : ℝ) * (N / l : ℕ) * (S + eta * (L - S)) / 2)) *
            (2 : ℝ) ^ ((N % l : ℕ) * L / 2) ≤ (2 : ℝ) ^ ((N : ℝ) * R / 2)) ∧
        ((1 / 2 : ℝ) ^ (N / l) ≤ 2 * Real.exp (-gamma * (N : ℝ))) := by
  obtain ⟨eta, l, heta0, heta1, hlmin, hl, he, hrate⟩ :=
    exists_fixed_block_parameters hepsilon hSR hRL minBlock
  refine ⟨eta, l, Real.log 2 / (l : ℝ), heta0, heta1, hlmin, hl, he, hrate,
    fixed_block_decay_rate_pos l hl, ?_⟩
  filter_upwards [eventually_padded_retained_cost_mul_le l hl (L := L) hrate] with N hcost
  exact ⟨hcost, half_pow_div_le_exponential N l hl⟩

end QuantumChannelStein.FixedBlockRates
