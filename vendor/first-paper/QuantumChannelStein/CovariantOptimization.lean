import QuantumChannelStein.CovariantOrbitRecovery
import QuantumChannelStein.SharpOptimizationReduction

/-! # Genuine permutation-covariant optimizer reduction

A coherent finite group flag and an actual controlled output recovery channel
prove the reduction from data processing alone. No optimizer existence,
concavity of the divergence, or covariance-reduction assumption is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.CovariantOptimization
open Matrix ChannelEntropy PureReferenceRecovery CovariantOrbitInput CovariantOrbitRecovery DivergenceOptimization
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {n m : ℕ}

def InvariantDensity (p : G →* Equiv.Perm (Fin n)) :=
  {ω : State n // ∀ g : G, Matrix.reindex (p g) (p g) ω.matrix = ω.matrix}

/-- An explicit invariant canonical input dominates any original pure test input. -/
theorem pure_le_invariant_canonical (D : StateDivergence) (hD : DataProcessing D)
    (p : G →* Equiv.Perm (Fin n)) (q : G →* Equiv.Perm (Fin m))
    (Φ Ψ : KrausChannel n m) (hΦ : Covariant p q Φ) (hΨ : Covariant p q Ψ)
    (ψ : UnitPureInput n n) :
    D (pureOutput Φ ψ) (pureOutput Ψ ψ) ≤
      D (pureOutput Φ (TestingPrimal.densityInput (averageDensity p (inputDensity ψ))))
        (pureOutput Ψ (TestingPrimal.densityInput (averageDensity p (inputDensity ψ)))) := by
  have hr := hD (recoveryChannel q) (pureOutput Φ (orbitInput p ψ)) (pureOutput Ψ (orbitInput p ψ))
  rw [recoveryChannel_pureOutput p q Φ hΦ ψ, recoveryChannel_pureOutput p q Ψ hΨ ψ] at hr
  have hc := pure_reference_le_canonical D hD Φ Ψ (orbitInput p ψ)
  rw [orbitInput_density] at hc
  exact hr.trans hc

/-- The covariant channel optimization may be restricted exactly to invariant density parameters. -/
theorem channelValue_eq_invariant_density_sup (D : StateDivergence) (hD : DataProcessing D)
    (p : G →* Equiv.Perm (Fin n)) (q : G →* Equiv.Perm (Fin m))
    (Φ Ψ : KrausChannel n m) (hΦ : Covariant p q Φ) (hΨ : Covariant p q Ψ) :
    channelValue D Φ Ψ = ⨆ ω : InvariantDensity p,
      D (pureOutput Φ (TestingPrimal.densityInput ω.val)) (pureOutput Ψ (TestingPrimal.densityInput ω.val)) := by
  apply le_antisymm
  · apply iSup_le
    intro ψ
    let ω : InvariantDensity p :=
      ⟨averageDensity p (inputDensity ψ), averageDensity_invariant p (inputDensity ψ)⟩
    exact (pure_le_invariant_canonical D hD p q Φ Ψ hΦ hΨ ψ).trans
      (le_iSup (fun ω : InvariantDensity p => D (pureOutput Φ (TestingPrimal.densityInput ω.val))
        (pureOutput Ψ (TestingPrimal.densityInput ω.val))) ω)
  · apply iSup_le
    intro ω
    exact le_iSup (fun ψ : UnitPureInput n n => D (pureOutput Φ ψ) (pureOutput Ψ ψ))
      (TestingPrimal.densityInput ω.val)

/-- Actual supported D-sharp satisfies the proved invariant optimizer reduction. -/
theorem sharp_channelValue_eq_invariant_density_sup (α : ℝ) (hα : 1 < α)
    (p : G →* Equiv.Perm (Fin n)) (q : G →* Equiv.Perm (Fin m))
    (Φ Ψ : KrausChannel n m) (hΦ : Covariant p q Φ) (hΨ : Covariant p q Ψ) :
    channelValue (fun ρ σ => SharpDivergence.divergence α hα ρ σ) Φ Ψ =
      ⨆ ω : InvariantDensity p, SharpDivergence.divergence α hα
        (pureOutput Φ (TestingPrimal.densityInput ω.val)) (pureOutput Ψ (TestingPrimal.densityInput ω.val)) :=
  channelValue_eq_invariant_density_sup (fun ρ σ => SharpDivergence.divergence α hα ρ σ)
    (fun Φ ρ σ => SharpDivergence.divergence_data_processing α hα Φ ρ σ) p q Φ Ψ hΦ hΨ

/-- The same concrete reduction applies to the actual sandwiched Rényi channel divergence. -/
theorem renyi_channelD_eq_invariant_density_sup (α : ℝ) (hα : 1 < α)
    (p : G →* Equiv.Perm (Fin n)) (q : G →* Equiv.Perm (Fin m))
    (Φ Ψ : KrausChannel n m) (hΦ : Covariant p q Φ) (hΨ : Covariant p q Ψ) :
    ChannelRenyi.channelD α hα Φ Ψ = ⨆ ω : InvariantDensity p,
      SandwichedRenyi.renyi α hα (pureOutput Φ (TestingPrimal.densityInput ω.val))
        (pureOutput Ψ (TestingPrimal.densityInput ω.val)) :=
  channelValue_eq_invariant_density_sup (fun ρ σ => SandwichedRenyi.renyi α hα ρ σ)
    (fun Φ ρ σ => SandwichedRenyi.renyi_data_processing α hα Φ ρ σ) p q Φ Ψ hΦ hΨ

end QuantumChannelStein.CovariantOptimization
