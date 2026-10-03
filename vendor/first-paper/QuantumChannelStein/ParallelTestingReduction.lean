import QuantumChannelStein.DivergenceOptimization
import QuantumChannelStein.AdaptiveCircuit
import QuantumChannelStein.ParallelConverse

/-! Exact probability-preserving normal form for every parallel test. -/
noncomputable section
namespace QuantumChannelStein.ParallelTestingReduction
open ChannelEntropy OperationalTesting PureReferenceRecovery MixedReferencePurification
  ParallelConverse
variable {a b : ℕ}

/-- One input-sized pure test preserves the acceptance of a given mixed,
arbitrary-reference test under every channel hypothesis simultaneously. -/
theorem exists_pure_test (t : ChannelTest a b) :
    ∃ ψ : UnitPureInput a a, ∃ T : Effect (a*b),
      ∀ Φ : KrausChannel a b, T.probability (pureOutput Φ ψ) = t.acceptance Φ := by
  let φ := purificationInput t.input
  let Tbig := ((traceFirst (t.reference*a) t.reference).tensor
    (KrausChannel.identity b)).pullbackEffect t.effect
  obtain ⟨Γ,hΓ⟩ := exists_output_reference_recovery (m := b) φ
  refine ⟨TestingPrimal.densityInput (inputDensity φ),
    (Γ.tensor (KrausChannel.identity b)).pullbackEffect Tbig, ?_⟩
  intro Φ
  rw [KrausChannel.pullbackEffect_probability, hΓ Φ]
  change (((traceFirst (t.reference*a) t.reference).tensor
    (KrausChannel.identity b)).pullbackEffect t.effect).probability
    (pureOutput Φ (purificationInput t.input)) = _
  rw [KrausChannel.pullbackEffect_probability, outputState_recovered]
  rfl

/-- The unrestricted finite-reference mixed optimum equals literal (2.4). -/
theorem parallelBeta_eq_parallelPureBeta (Φ Ψ : KrausChannel a b) (k : ℕ) (ε : ℝ) :
    parallelBeta Φ Ψ k ε = parallelPureBeta Φ Ψ k ε := by
  apply le_antisymm (parallelBeta_le_parallelPureBeta Φ Ψ k ε)
  apply le_iInf
  intro t
  obtain ⟨ψ,T,h⟩ := exists_pure_test t.val
  refine iInf_le_of_le ⟨(ψ,T), ?_⟩ ?_
  · rw [h]
    exact t.property
  · rw [h]

/-- Proposition 3.5's converse is uniform over all actual parallel tests,
including mixed inputs and arbitrary finite reference sizes. -/
theorem proposition_3_5_all_parallel_converse (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤)
    (R : ℝ) (hR : (ChannelEntropy.regularizedD Φ Ψ).toReal < R) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : ChannelTest (a^n) (b^n),
        t.acceptance (Ψ.tensorPower n) ≤ (2 : ℝ)^(-(n : ℝ)*R) →
        t.acceptance (Φ.tensorPower n) ≤ K * Real.exp (-γ*n) := by
  obtain ⟨K,γ,hK,hγ,N,h⟩ := proposition_3_5_exponential_converse Φ Ψ ha hfinite R hR
  refine ⟨K,γ,hK,hγ,N,?_⟩
  intro n hn t hq
  obtain ⟨ψ,T,hT⟩ := exists_pure_test t
  have hp := h n hn ψ T
  rw [hT, hT] at hp
  exact hp hq

end QuantumChannelStein.ParallelTestingReduction
