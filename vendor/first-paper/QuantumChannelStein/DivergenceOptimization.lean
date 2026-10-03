import QuantumChannelStein.MixedReferencePurification
import QuantumChannelStein.ChannelRenyi

/-! # Genuine reference and mixed-input reductions for data-processing divergences

The generic theorems take only the explicitly stated data-processing property.
Their final Rényi and Umegaki instances use the proved actual Kraus-channel DPI.
Recovery channels and purifications are constructed, never postulated.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.DivergenceOptimization
open Matrix ChannelEntropy OperationalTesting PureReferenceRecovery MixedReferencePurification
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

abbrev StateDivergence := ∀ {n : ℕ}, State n → State n → EReal

def DataProcessing (D : StateDivergence) : Prop :=
  ∀ {n m : ℕ}, ∀ Φ : KrausChannel n m, ∀ ρ σ : State n,
    D (Φ.onState ρ) (Φ.onState σ) ≤ D ρ σ

def channelValue (D : StateDivergence) {n m : ℕ} (Φ Ψ : KrausChannel n m) : EReal :=
  ⨆ ψ : UnitPureInput n n, D (pureOutput Φ ψ) (pureOutput Ψ ψ)

variable {n m r : ℕ}

theorem outputState_pureInputState (Φ : KrausChannel n m) (ψ : UnitPureInput r n) :
    outputState Φ r (pureInputState ψ) = pureOutput Φ ψ :=
  state_eq_of_matrix_eq _ _ (outputState_pureInputState_matrix Φ ψ)

/-- Every finite reference is dominated by a canonical input-sized purification. -/
theorem pure_reference_le_canonical (D : StateDivergence) (hD : DataProcessing D)
    (Φ Ψ : KrausChannel n m) (ψ : UnitPureInput r n) :
    D (pureOutput Φ ψ) (pureOutput Ψ ψ) ≤
      D (pureOutput Φ (TestingPrimal.densityInput (inputDensity ψ)))
        (pureOutput Ψ (TestingPrimal.densityInput (inputDensity ψ))) := by
  obtain ⟨Γ, hΓ⟩ := exists_output_reference_recovery (m := m) ψ
  have h := hD (Γ.tensor (KrausChannel.identity m))
    (pureOutput Φ (TestingPrimal.densityInput (inputDensity ψ)))
    (pureOutput Ψ (TestingPrimal.densityInput (inputDensity ψ)))
  rwa [hΓ Φ, hΓ Ψ] at h

/-- Arbitrary finite pure references do not enlarge the exact channel optimization. -/
theorem pure_reference_le_channelValue (D : StateDivergence) (hD : DataProcessing D)
    (Φ Ψ : KrausChannel n m) (ψ : UnitPureInput r n) :
    D (pureOutput Φ ψ) (pureOutput Ψ ψ) ≤ channelValue D Φ Ψ :=
  (pure_reference_le_canonical D hD Φ Ψ ψ).trans
    (le_iSup (fun φ : UnitPureInput n n => D (pureOutput Φ φ) (pureOutput Ψ φ))
      (TestingPrimal.densityInput (inputDensity ψ)))

/-- Arbitrary mixed inputs and arbitrary finite references are bounded by the pure-reference supremum. -/
theorem mixed_reference_le_channelValue (D : StateDivergence) (hD : DataProcessing D)
    (Φ Ψ : KrausChannel n m) (ρ : State (r * n)) :
    D (outputState Φ r ρ) (outputState Ψ r ρ) ≤ channelValue D Φ Ψ := by
  have h := hD ((traceFirst (r * n) r).tensor (KrausChannel.identity m))
    (pureOutput Φ (purificationInput ρ)) (pureOutput Ψ (purificationInput ρ))
  rw [outputState_recovered, outputState_recovered] at h
  exact h.trans (pure_reference_le_channelValue D hD Φ Ψ (purificationInput ρ))

/-- The exact pure optimization equals optimization over density matrices via their canonical purifications. -/
theorem channelValue_eq_density_sup (D : StateDivergence) (hD : DataProcessing D)
    (Φ Ψ : KrausChannel n m) :
    channelValue D Φ Ψ = ⨆ ω : State n,
      D (pureOutput Φ (TestingPrimal.densityInput ω)) (pureOutput Ψ (TestingPrimal.densityInput ω)) := by
  apply le_antisymm
  · apply iSup_le
    intro ψ
    exact (pure_reference_le_canonical D hD Φ Ψ ψ).trans
      (le_iSup (fun ω : State n => D (pureOutput Φ (TestingPrimal.densityInput ω))
        (pureOutput Ψ (TestingPrimal.densityInput ω))) (inputDensity ψ))
  · apply iSup_le
    intro ω
    exact le_iSup (fun ψ : UnitPureInput n n => D (pureOutput Φ ψ) (pureOutput Ψ ψ))
      (TestingPrimal.densityInput ω)

/-- The exact supremum is unchanged by allowing every finite reference and every mixed input. -/
theorem mixed_reference_sup_eq (D : StateDivergence) (hD : DataProcessing D)
    (Φ Ψ : KrausChannel n m) :
    (⨆ r : ℕ, ⨆ ρ : State (r * n), D (outputState Φ r ρ) (outputState Ψ r ρ)) = channelValue D Φ Ψ := by
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro ρ
    exact mixed_reference_le_channelValue D hD Φ Ψ ρ
  · apply iSup_le
    intro ψ
    apply le_iSup_of_le n
    apply le_iSup_of_le (pureInputState ψ)
    rw [outputState_pureInputState, outputState_pureInputState]

/-- Concrete Choi representation of the canonical optimizing output. -/
theorem canonical_output_matrix (Φ : KrausChannel n m) (ω : State n) :
    (pureOutput Φ (TestingPrimal.densityInput ω)).matrix =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((CFC.sqrt ω.matrix ⊗ₖ (1 : Operator m)) * Φ.choi *
          (CFC.sqrt ω.matrix ⊗ₖ (1 : Operator m))ᴴ) := by
  rw [pureOutput_matrix]
  exact congrArg (Matrix.reindex finProdFinEquiv finProdFinEquiv)
    (TestingPrimal.amplify_coefficientVector Φ (CFC.sqrt ω.matrix))

/-- The sandwiched Rényi instance uses the proved all-state DPI. -/
theorem renyi_mixed_reference_le (α : ℝ) (hα : 1 < α)
    (Φ Ψ : KrausChannel n m) (ρ : State (r * n)) :
    SandwichedRenyi.renyi α hα (outputState Φ r ρ) (outputState Ψ r ρ) ≤
      ChannelRenyi.channelD α hα Φ Ψ := by
  exact mixed_reference_le_channelValue (fun ρ σ => SandwichedRenyi.renyi α hα ρ σ)
    (fun Φ ρ σ => SandwichedRenyi.renyi_data_processing α hα Φ ρ σ) Φ Ψ ρ

/-- The Umegaki instance also includes all singular and infinite branches. -/
theorem umegaki_mixed_reference_le (Φ Ψ : KrausChannel n m) (ρ : State (r * n)) :
    RelativeEntropy.umegaki (outputState Φ r ρ) (outputState Ψ r ρ) ≤ ChannelEntropy.channelD Φ Ψ := by
  exact mixed_reference_le_channelValue (fun ρ σ => RelativeEntropy.umegaki ρ σ)
    (fun Φ ρ σ => RelativeEntropy.umegaki_data_processing Φ ρ σ) Φ Ψ ρ

theorem renyi_channelD_eq_density_sup (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m) :
    ChannelRenyi.channelD α hα Φ Ψ = ⨆ ω : State n,
      SandwichedRenyi.renyi α hα (pureOutput Φ (TestingPrimal.densityInput ω))
        (pureOutput Ψ (TestingPrimal.densityInput ω)) :=
  channelValue_eq_density_sup (fun ρ σ => SandwichedRenyi.renyi α hα ρ σ)
    (fun Φ ρ σ => SandwichedRenyi.renyi_data_processing α hα Φ ρ σ) Φ Ψ

end QuantumChannelStein.DivergenceOptimization
