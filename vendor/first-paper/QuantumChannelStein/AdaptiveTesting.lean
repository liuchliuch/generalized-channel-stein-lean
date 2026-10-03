import QuantumChannelStein.ParallelAdaptiveEmbedding
import QuantumChannelStein.AdaptiveConverse
import QuantumChannelStein.ParallelExponent
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Actual adaptive testing optimization and its conditional converse

The infimum ranges over the genuine finite-memory protocols. Inclusion of
the paper's parallel pure tests is proved by their concrete sequential
compilation, not built into the definition by assumption.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.AdaptiveProtocol
open ChannelEntropy OperationalTesting ParallelExponent Filter
open scoped Topology
variable {a b : ℕ}

/-- Actual adaptive type-II optimum under the fixed type-I constraint. -/
def adaptiveBeta (Φ Ψ : KrausChannel a b) (k : ℕ) (ε : ℝ) : ENNReal :=
  ⨅ P : {P : Protocol a b k // 1 - ε ≤ P.acceptance Φ}, ENNReal.ofReal (P.val.acceptance Ψ)

/-- Genuine sequential embedding supplies the operational comparison of optima. -/
theorem adaptiveBeta_le_parallelPureBeta (Φ Ψ : KrausChannel a b) (k : ℕ) (ε : ℝ) :
    adaptiveBeta Φ Ψ k ε ≤ parallelPureBeta Φ Ψ k ε := by
  apply le_iInf
  intro t
  let P := parallelProtocol k t.val.1 t.val.2
  have hp : 1 - ε ≤ P.acceptance Φ := by
    rw [parallelProtocol_acceptance]
    exact t.property
  have hle : adaptiveBeta Φ Ψ k ε ≤ ENNReal.ofReal (P.acceptance Ψ) :=
    iInf_le_of_le ⟨P, hp⟩ le_rfl
  exact hle.trans_eq (congrArg ENNReal.ofReal (parallelProtocol_acceptance Ψ k t.val.1 t.val.2))

theorem adaptiveBeta_le_one (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) : adaptiveBeta Φ Ψ k ε ≤ 1 :=
  (adaptiveBeta_le_parallelPureBeta Φ Ψ k ε).trans (parallelPureBeta_le_one Φ Ψ ha k ε hε)

/-- A real parallel zero-error test also gives an adaptive zero-error optimum. -/
theorem adaptiveBeta_eq_zero_of_parallel (Φ Ψ : KrausChannel a b) (k : ℕ) (ε : ℝ)
    (h : parallelPureBeta Φ Ψ k ε = 0) : adaptiveBeta Φ Ψ k ε = 0 :=
  le_antisymm ((adaptiveBeta_le_parallelPureBeta Φ Ψ k ε).trans_eq h) bot_le

/-- The adaptive exponent uses the same correct extended negative logarithm. -/
def adaptiveErrorExponent (Φ Ψ : KrausChannel a b) (ε : ℝ) (k : ℕ) : EReal :=
  testingExponent k (adaptiveBeta Φ Ψ k ε)

/-- Parallel achievability transfers through the actual probability-preserving embedding. -/
theorem parallelErrorExponent_le_adaptiveErrorExponent (Φ Ψ : KrausChannel a b) (ε : ℝ) (k : ℕ) :
    parallelErrorExponent Φ Ψ ε k ≤ adaptiveErrorExponent Φ Ψ ε k :=
  testingExponent_antitone k (adaptiveBeta_le_parallelPureBeta Φ Ψ k ε)

/-- The actual uniform adaptive converse forces every feasible test's type-II
probability to have each strict upper exponent above the Umegaki rate. -/
theorem eventually_adaptiveBeta_lower_of_chain (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤)
    (hchain : ∀ (α : ℝ) (hα : 1 < α), α ≤ 2 → HasRenyiChannelChain α hα Φ Ψ)
    (ε : ℝ) (hε : ε < 1) (R : ℝ) (hR : (ChannelEntropy.regularizedD Φ Ψ).toReal < R) :
    ∀ᶠ k : ℕ in atTop, ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) * R)) ≤ adaptiveBeta Φ Ψ k ε := by
  obtain ⟨c, hc, hbound⟩ := adaptive_exponential_converse_of_chain Φ Ψ ha hfinite hchain R hR
  have hlim : Tendsto (fun k : ℕ => (2 : ℝ) ^ (-(k : ℝ) * c)) atTop (𝓝 0) := by
    have h := TwoRateScalars.stretched_error_tendsto_zero 1
      (mul_pos hc (Real.log_pos (by norm_num : (1 : ℝ) < 2))) (by norm_num : (0 : ℝ) < 1)
    convert h using 1
    ext k
    simp only [Real.rpow_one, one_mul]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hsmall := hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - ε))
  filter_upwards [eventually_gt_atTop (0 : ℕ), hsmall] with k hk hsmallk
  apply le_iInf
  intro P
  apply ENNReal.ofReal_le_ofReal
  by_contra! hlt
  have hp := hbound k hk P.val hlt.le
  linarith [P.property]

theorem eventually_adaptiveErrorExponent_le_of_chain (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤)
    (hchain : ∀ (α : ℝ) (hα : 1 < α), α ≤ 2 → HasRenyiChannelChain α hα Φ Ψ)
    (ε : ℝ) (hε : ε < 1) (R : ℝ) (hR : (ChannelEntropy.regularizedD Φ Ψ).toReal < R) :
    ∀ᶠ k : ℕ in atTop, adaptiveErrorExponent Φ Ψ ε k ≤ (R : EReal) := by
  filter_upwards [eventually_adaptiveBeta_lower_of_chain Φ Ψ ha hfinite hchain ε hε R hR,
    eventually_gt_atTop (0 : ℕ)] with k hk hkpos
  exact (testingExponent_antitone k hk).trans_eq (testingExponent_two_rpow k hkpos R)

/-- The conditional fixed-error converse for the actual adaptive optimum. -/
theorem limsup_adaptiveErrorExponent_le_of_chain (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤)
    (hchain : ∀ (α : ℝ) (hα : 1 < α), α ≤ 2 → HasRenyiChannelChain α hα Φ Ψ)
    (ε : ℝ) (hε : ε < 1) :
    limsup (adaptiveErrorExponent Φ Ψ ε) atTop ≤ ChannelEntropy.regularizedD Φ Ψ := by
  have hbot : ChannelEntropy.regularizedD Φ Ψ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (ChannelEntropy.regularizedD_nonneg Φ Ψ ha))
  have hreg := EReal.coe_toReal hfinite.ne hbot
  by_contra! hlt
  obtain ⟨R, hdR, hRlim⟩ := EReal.exists_between_coe_real hlt
  have hdR' : (ChannelEntropy.regularizedD Φ Ψ).toReal < R := by
    rw [← hreg] at hdR
    exact EReal.coe_lt_coe_iff.mp hdR
  have hle : limsup (adaptiveErrorExponent Φ Ψ ε) atTop ≤ (R : EReal) :=
    limsup_le_of_le (by isBoundedDefault)
      (eventually_adaptiveErrorExponent_le_of_chain Φ Ψ ha hfinite hchain ε hε R hdR')
  exact (not_lt_of_ge hle) hRlim

/-- Assembly helper: once the genuine parallel Stein limit and one-shot chain
rule are supplied, the actual adaptive fixed-error limit follows. -/
theorem adaptive_limit_of_parallel_limit_and_chain (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤)
    (hchain : ∀ (α : ℝ) (hα : 1 < α), α ≤ 2 → HasRenyiChannelChain α hα Φ Ψ)
    (ε : ℝ) (hε : ε < 1)
    (hparallel : Tendsto (parallelErrorExponent Φ Ψ ε) atTop (𝓝 (ChannelEntropy.regularizedD Φ Ψ))) :
    Tendsto (adaptiveErrorExponent Φ Ψ ε) atTop (𝓝 (ChannelEntropy.regularizedD Φ Ψ)) := by
  apply tendsto_of_le_liminf_of_limsup_le _ (limsup_adaptiveErrorExponent_le_of_chain Φ Ψ ha hfinite hchain ε hε)
  rw [← hparallel.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall (parallelErrorExponent_le_adaptiveErrorExponent Φ Ψ ε))

/-- Infinite actual channel divergence gives eventually zero adaptive type-II
error by embedding the checked concrete support-failure parallel tests. -/
theorem adaptiveBeta_eventually_zero_of_infinite (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hinfinite : ChannelEntropy.regularizedD Φ Ψ = ⊤)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ k : ℕ in atTop, adaptiveBeta Φ Ψ k ε = 0 := by
  have hsupport : ¬ LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin := by
    rw [← ChannelEntropy.regularizedD_lt_top_iff_choi_support Φ Ψ ha, hinfinite]
    exact not_lt_of_ge le_rfl
  filter_upwards [(OperationalTesting.proposition_3_6 Φ Ψ ha hsupport).2 ε hε hε1] with k hk
  exact adaptiveBeta_eq_zero_of_parallel Φ Ψ k ε hk

/-- The infinite-divergence adaptive exponent limit is unconditional; no
channel-chain premise or state-Stein asymptotic input is needed. -/
theorem adaptiveErrorExponent_tendsto_top_of_infinite (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hinfinite : ChannelEntropy.regularizedD Φ Ψ = ⊤)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (adaptiveErrorExponent Φ Ψ ε) atTop (𝓝 ⊤) := by
  have heq : ∀ᶠ k : ℕ in atTop, adaptiveErrorExponent Φ Ψ ε k = ⊤ := by
    filter_upwards [adaptiveBeta_eventually_zero_of_infinite Φ Ψ ha hinfinite ε hε hε1,
      eventually_gt_atTop (0 : ℕ)] with k hk hkpos
    rw [adaptiveErrorExponent, hk, testingExponent_zero hkpos]
  exact tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm))

end QuantumChannelStein.AdaptiveProtocol
