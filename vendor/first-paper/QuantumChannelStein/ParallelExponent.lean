import QuantumChannelStein.ParallelConverse
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Data.EReal.Inv
import Mathlib.Order.LiminfLimsup

/-!
# Extended operational error exponents: the converse part of Proposition 3.5

The logarithm is genuinely extended: a zero type-II optimum has exponent
positive infinity at every positive blocklength. No real-valued `log 0`
convention is used. The operational infimum is the literal fixed-reference
pure-test optimization, not a relaxation.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ParallelExponent
open scoped Topology
open Filter ChannelEntropy OperationalTesting ParallelConverse
variable {a b : ℕ}

/-- Normalized base-two negative logarithm, extended to zero and infinity.
At blocklength zero the finite scalar prefactor is zero. -/
def testingExponent (k : ℕ) (β : ENNReal) : EReal :=
  (((1 / ((k : ℝ) * Real.log 2)) : ℝ) : EReal) * (-ENNReal.log β)

/-- A zero type-II probability has exponent positive infinity. -/
theorem testingExponent_zero {k : ℕ} (hk : 0 < k) : testingExponent k 0 = ⊤ := by
  have hc : 0 < 1 / ((k : ℝ) * Real.log 2) :=
    one_div_pos.mpr (mul_pos (Nat.cast_pos.mpr hk) (Real.log_pos (by norm_num)))
  simp only [testingExponent, ENNReal.log_zero, EReal.neg_bot]
  exact EReal.coe_mul_top_of_pos hc

@[simp] theorem testingExponent_one (k : ℕ) : testingExponent k 1 = 0 := by
  simp [testingExponent]

/-- The true extended error exponent decreases with the type-II probability. -/
theorem testingExponent_antitone (k : ℕ) : Antitone (testingExponent k) := by
  intro x y hxy
  unfold testingExponent
  apply mul_le_mul_of_nonneg_left (EReal.neg_le_neg_iff.mpr (ENNReal.log_le_log hxy))
  exact EReal.coe_nonneg.mpr (one_div_nonneg.mpr
    (mul_nonneg (Nat.cast_nonneg k) (Real.log_pos (by norm_num)).le))

/-- Agreement with the familiar finite normalized negative logarithm. -/
theorem testingExponent_ofReal {x : ℝ} (hx : 0 < x) (k : ℕ) :
    testingExponent k (ENNReal.ofReal x) =
      ((-Real.log x / ((k : ℝ) * Real.log 2) : ℝ) : EReal) := by
  rw [testingExponent, ENNReal.log_ofReal_of_pos hx, ← EReal.coe_neg, ← EReal.coe_mul]
  congr 1
  ring

/-- An exponentially small type-II probability has exactly its stated rate. -/
theorem testingExponent_two_rpow (k : ℕ) (hk : 0 < k) (R : ℝ) :
    testingExponent k (ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) * R))) = (R : EReal) := by
  rw [testingExponent_ofReal (by positivity), Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  congr 1
  have hk' : (k : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp

/-- The literal paper's parallel type-II error exponent. -/
def parallelErrorExponent (Φ Ψ : KrausChannel a b) (ε : ℝ) (k : ℕ) : EReal :=
  testingExponent k (parallelPureBeta Φ Ψ k ε)

/-- Uniform exponential rejection supplies each eventual strict upper rate
for the actual optimized fixed-error exponent. -/
theorem eventually_parallelErrorExponent_le (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (ε : ℝ) (hε : ε < 1) (R : ℝ)
    (hR : (regularizedD Φ Ψ).toReal < R) :
    ∀ᶠ k : ℕ in atTop, parallelErrorExponent Φ Ψ ε k ≤ (R : EReal) := by
  filter_upwards [eventually_parallelPureBeta_lower Φ Ψ ha hfinite ε hε R hR,
    eventually_gt_atTop (0 : ℕ)] with k hk hkpos
  exact (testingExponent_antitone k hk).trans_eq (testingExponent_two_rpow k hkpos R)

/-- The converse half of Proposition 3.5: the limsup of the correctly extended
fixed-error operational exponent is at most the regularized channel relative
entropy. The matching achievability statement is separate. -/
theorem proposition_3_5_limsup_le (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (ε : ℝ) (_hε0 : 0 < ε) (hε1 : ε < 1) :
    limsup (parallelErrorExponent Φ Ψ ε) atTop ≤ regularizedD Φ Ψ := by
  have hbot : regularizedD Φ Ψ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (regularizedD_nonneg Φ Ψ ha))
  have hreg : regularizedD Φ Ψ = ((regularizedD Φ Ψ).toReal : EReal) :=
    (EReal.coe_toReal hfinite.ne hbot).symm
  by_contra! hlt
  obtain ⟨R, hdR, hRlim⟩ := EReal.exists_between_coe_real hlt
  have hdR' : (regularizedD Φ Ψ).toReal < R := by
    rw [hreg] at hdR
    exact EReal.coe_lt_coe_iff.mp hdR
  have hle : limsup (parallelErrorExponent Φ Ψ ε) atTop ≤ (R : EReal) :=
    limsup_le_of_le (by isBoundedDefault)
      (eventually_parallelErrorExponent_le Φ Ψ ha hfinite ε hε1 R hdR')
  exact (not_lt_of_ge hle) hRlim

end QuantumChannelStein.ParallelExponent
