import QuantumChannelStein.DivergenceOptimization
import QuantumChannelStein.SharpDataProcessing

/-! # The actual supported D-sharp instance of the proved optimization reduction -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SharpDivergence
open ChannelEntropy OperationalTesting DivergenceOptimization
variable {n m r : ℕ}

theorem mixed_reference_le_channelValue (α : ℝ) (hα : 1 < α)
    (Φ Ψ : KrausChannel n m) (ρ : State (r * n)) :
    divergence α hα (outputState Φ r ρ) (outputState Ψ r ρ) ≤
      channelValue (fun ρ σ => divergence α hα ρ σ) Φ Ψ :=
  DivergenceOptimization.mixed_reference_le_channelValue (fun ρ σ => divergence α hα ρ σ)
    (fun Φ ρ σ => divergence_data_processing α hα Φ ρ σ) Φ Ψ ρ

theorem channelValue_eq_canonical_density_sup (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m) :
    channelValue (fun ρ σ => divergence α hα ρ σ) Φ Ψ = ⨆ ω : State n,
      divergence α hα (pureOutput Φ (TestingPrimal.densityInput ω))
        (pureOutput Ψ (TestingPrimal.densityInput ω)) :=
  DivergenceOptimization.channelValue_eq_density_sup (fun ρ σ => divergence α hα ρ σ)
    (fun Φ ρ σ => divergence_data_processing α hα Φ ρ σ) Φ Ψ

end QuantumChannelStein.SharpDivergence
