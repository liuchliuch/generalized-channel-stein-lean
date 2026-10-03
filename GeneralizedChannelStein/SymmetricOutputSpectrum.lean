import GeneralizedChannelStein.SymmetricSpectralCount
import GeneralizedChannelStein.CanonicalInput
import QuantumChannelStein.CanonicalOutputSpectralBound
import QuantumChannelStein.SpectralPinching

/-! # Exact binomial spectral bound for correlated covariant alternatives -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.SymmetricOutputSpectrum
open QuantumChannelStein Matrix TensorPower TensorPermutation ChannelPowerReindex ChannelEntropy
open TensorChannelCovariance CovariantOptimization
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- Regroup the actual paired reference/output sites, with no product assumption on the state. -/
def invariantState (k : ℕ) (σ : State (a^k*b^k))
    (hσ : ∀ p : Equiv.Perm (Fin k),
      Matrix.reindex (outputReindex (channelPermutation a k p) (channelPermutation b k p))
      (outputReindex (channelPermutation a k p) (channelPermutation b k p)) σ.matrix = σ.matrix) :
    invariantAlgebra (Fin a × Fin b) k := by
  refine ⟨Matrix.reindex (outputIndexEquiv a b k).symm (outputIndexEquiv a b k).symm σ.matrix, ?_⟩
  intro p
  ext i j
  change σ.matrix (outputIndexEquiv a b k ((factorPermutation (Fin a × Fin b) k p).symm i))
    (outputIndexEquiv a b k ((factorPermutation (Fin a × Fin b) k p).symm j)) =
      σ.matrix (outputIndexEquiv a b k i) (outputIndexEquiv a b k j)
  rw [outputIndexEquiv_symm_factorPermutation, outputIndexEquiv_symm_factorPermutation]
  exact congrFun (congrFun (hσ p) (outputIndexEquiv a b k i)) (outputIndexEquiv a b k j)

theorem spectrum_card_le_binomial (ha : 0<a) (hb : 0<b) (k : ℕ) (σ : State (a^k*b^k))
    (hσ : ∀ p : Equiv.Perm (Fin k),
      Matrix.reindex (outputReindex (channelPermutation a k p) (channelPermutation b k p))
      (outputReindex (channelPermutation a k p) (channelPermutation b k p)) σ.matrix = σ.matrix) :
    (spectrum ℂ σ.matrix).ncard ≤ (k+(a*b)^2-1).choose ((a*b)^2-1) := by
  have heq : spectrum ℂ (invariantState k σ hσ).val = spectrum ℂ σ.matrix := by
    change spectrum ℂ ((Matrix.reindexAlgEquiv ℂ ℂ (outputIndexEquiv a b k).symm) σ.matrix) = _
    exact AlgEquiv.spectrum_eq _ _
  rw [← heq]
  have h := (SymmetricSpectralCount.ncard_spectrum_le_finrank k (invariantState k σ hσ)).trans
    (InvariantOrbitDimension.finrank_invariantAlgebra_le_choose (Fin a × Fin b) k)
  simp only [Fintype.card_prod, Fintype.card_fin, ← pow_two] at h
  have hpos : 0 < (a*b)^2 := pow_pos (Nat.mul_pos ha hb) _
  have he : (a*b)^2+k-1 = k+((a*b)^2-1) := by omega
  have he' : k+(a*b)^2-1 = k+((a*b)^2-1) := by omega
  rw [he, Nat.choose_symm_add] at h
  simpa only [he'] using h

/-- Covariance and an invariant physical input marginal imply invariance of the actual output. -/
theorem canonical_output_invariant (k : ℕ) (M : KrausChannel (a^k) (b^k))
    (hM : CovariantOrbitRecovery.Covariant (channelPermutation a k) (channelPermutation b k) M)
    (ρ : State (a^k))
    (hρ : ∀ p : Equiv.Perm (Fin k),
      Matrix.reindex (channelPermutation a k p) (channelPermutation a k p) ρ.matrix = ρ.matrix)
    (p : Equiv.Perm (Fin k)) :
    Matrix.reindex (outputReindex (channelPermutation a k p) (channelPermutation b k p))
      (outputReindex (channelPermutation a k p) (channelPermutation b k p))
      (CanonicalInput.output M ρ).matrix = (CanonicalInput.output M ρ).matrix := by
  let ω : InvariantDensity (channelPermutation a k) := ⟨CanonicalInput.transposeState ρ, by
    intro g
    exact congrArg Matrix.transpose (hρ g)⟩
  exact congrArg State.matrix (canonicalOutput_invariant _ _ M hM ω p)

/-- Correlated block alternatives have the same sharp spectral bound as product channels. -/
theorem canonical_block_card_le (ha : 0<a) (hb : 0<b) (k : ℕ)
    (M : KrausChannel (a^k) (b^k))
    (hM : CovariantOrbitRecovery.Covariant (channelPermutation a k) (channelPermutation b k) M)
    (ρ : State (a^k))
    (hρ : ∀ p : Equiv.Perm (Fin k),
      Matrix.reindex (channelPermutation a k p) (channelPermutation a k p) ρ.matrix = ρ.matrix) :
    Fintype.card (SpectralPinching.Block (CanonicalInput.output M ρ)) ≤
      (k+(a*b)^2-1).choose ((a*b)^2-1) := by
  rw [SpectralPinching.block_card_eq_complex_spectrum]
  exact spectrum_card_le_binomial ha hb k _ (canonical_output_invariant k M hM ρ hρ)

end GeneralizedChannelStein.SymmetricOutputSpectrum
