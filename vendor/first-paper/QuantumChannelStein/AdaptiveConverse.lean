import QuantumChannelStein.AdaptiveProtocol
import QuantumChannelStein.BinaryRenyiTesting
import QuantumChannelStein.ChannelRenyiRightUpper

/-!
# Actual adaptive exponential converse, conditional only on the channel chain rule

The protocol semantics, state data processing, binary measurement, endpoint
handling, and scalar rearrangement are all proved. The remaining external
one-shot channel chain inequality is explicit in every adaptive theorem.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.AdaptiveProtocol
open Matrix SandwichedRenyi BinaryRenyiTesting ChannelEntropy Filter
open scoped Topology
variable {a b n m : ℕ}

/-- The actual binary test bound for any two final density matrices with a
finite Rényi upper bound, including the p=0 and q=0 endpoint cases. -/
theorem state_acceptance_le_two_rpow (α : ℝ) (hα : 1 < α)
    (ρ σ : State m) (T : Effect m) (n : ℕ) (hn : 0 < n) (d R : ℝ) (hR : 0 < R)
    (hD : renyi α hα ρ σ ≤ (((n : ℝ) * d : ℝ) : EReal))
    (hq : T.probability σ ≤ (2 : ℝ) ^ (-(n : ℝ) * R)) :
    T.probability ρ ≤ (2 : ℝ) ^ (-(n : ℝ) * (((α - 1) / α) * (R - d))) := by
  by_cases hp0 : T.probability ρ = 0
  · rw [hp0]
    positivity
  · have hp : 0 < T.probability ρ := lt_of_le_of_ne (T.probability_nonneg ρ) (Ne.symm hp0)
    have hqp : 0 < T.probability σ := alternative_positive_of_renyi_le α hα ρ σ T _ hD hp
    have hq1 : T.probability σ < 1 := hq.trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (by have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn; nlinarith))
    have hlog := logarithmic_test_bound α hα ρ σ T ((n : ℝ) * d) hD hp hq1
    have hqexp : T.probability σ ≤ Real.exp (-(n : ℝ) * R * Real.log 2) := by
      convert hq using 1
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have h := ScalarBounds.adaptive_acceptance_le_exponential hp hqp hα hlog hqexp
    apply h.trans_eq
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring

/-- Every actual finite-memory adaptive protocol obeys the binary exponential
bound at a fixed Rényi order, conditional on its genuine channel chain rule. -/
theorem Protocol.acceptance_le_two_rpow_of_chain (P : Protocol a b n)
    (Φ Ψ : KrausChannel a b) (ha : 0 < a) (hn : 0 < n)
    (α : ℝ) (hα : 1 < α) (hchain : HasRenyiChannelChain α hα Φ Ψ)
    (d R : ℝ) (hd : ChannelRenyi.regularizedD α hα Φ Ψ ≤ (d : EReal)) (hgap : d < R)
    (hq : P.acceptance Ψ ≤ (2 : ℝ) ^ (-(n : ℝ) * R)) :
    P.acceptance Φ ≤ (2 : ℝ) ^ (-(n : ℝ) * (((α - 1) / α) * (R - d))) := by
  have hd0 : 0 ≤ d := EReal.coe_nonneg.mp ((ChannelRenyi.regularizedD_nonneg α hα Φ Ψ ha).trans hd)
  exact state_acceptance_le_two_rpow α hα (P.finalState Φ) (P.finalState Ψ) P.effect n hn d R
    (hd0.trans_lt hgap) (P.finalState_renyi_le Φ Ψ α hα hchain d hd) hq

/-- Supporting version of the exponential assertion (2.6). The sole
remaining analytic hypothesis is the explicitly labelled one-shot channel
chain rule; it is not named an unconditional Theorem 2.1. The constants
are uniform over all blocklengths and all finite-memory strategies. -/
theorem adaptive_exponential_converse_of_chain
    (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤)
    (hchain : ∀ (α : ℝ) (hα : 1 < α), α ≤ 2 → HasRenyiChannelChain α hα Φ Ψ)
    (R : ℝ) (hR : (ChannelEntropy.regularizedD Φ Ψ).toReal < R) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → ∀ P : Protocol a b n,
      P.acceptance Ψ ≤ (2 : ℝ) ^ (-(n : ℝ) * R) →
      P.acceptance Φ ≤ (2 : ℝ) ^ (-(n : ℝ) * c) := by
  have hbot : ChannelEntropy.regularizedD Φ Ψ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (ChannelEntropy.regularizedD_nonneg Φ Ψ ha))
  have hreg := EReal.coe_toReal hfinite.ne hbot
  have hRext : ChannelEntropy.regularizedD Φ Ψ < (R : EReal) := by
    rw [← hreg]
    exact EReal.coe_lt_coe_iff.mpr hR
  have hsmall := ChannelRenyi.eventually_regularizedDAt_lt Φ Ψ ha hfinite (R : EReal) hRext
  have htwo : ∀ᶠ α : ℝ in 𝓝[>] (1 : ℝ), α < 2 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hgood : ∀ᶠ α : ℝ in 𝓝[>] (1 : ℝ),
      1 < α ∧ α ≤ 2 ∧ ChannelRenyi.regularizedDAt Φ Ψ α < (R : EReal) := by
    filter_upwards [self_mem_nhdsWithin, htwo, hsmall] with α hα hα2 hval
    exact ⟨hα, hα2.le, hval⟩
  obtain ⟨α, hα, hα2, hval⟩ := hgood.exists
  rw [ChannelRenyi.regularizedDAt_of_gt_one Φ Ψ α hα] at hval
  let d : ℝ := (ChannelRenyi.regularizedD α hα Φ Ψ).toReal
  have hdt : ChannelRenyi.regularizedD α hα Φ Ψ ≠ ⊤ := ne_of_lt (hval.trans (EReal.coe_lt_top R))
  have hdb : ChannelRenyi.regularizedD α hα Φ Ψ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (ChannelRenyi.regularizedD_nonneg α hα Φ Ψ ha))
  have hd : (d : EReal) = ChannelRenyi.regularizedD α hα Φ Ψ := EReal.coe_toReal hdt hdb
  have hdR : d < R := EReal.coe_lt_coe_iff.mp (by rwa [hd])
  refine ⟨((α - 1) / α) * (R - d), ScalarBounds.adaptive_decay_rate_pos hα hdR, ?_⟩
  intro n hn P hq
  exact P.acceptance_le_two_rpow_of_chain Φ Ψ ha hn α hα (hchain α hα hα2) d R hd.symm.le hdR hq

end QuantumChannelStein.AdaptiveProtocol
