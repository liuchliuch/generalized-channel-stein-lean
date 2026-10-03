import QuantumChannelStein.CanonicalCovariantOutput
import QuantumChannelStein.InvariantSpectralBound

/-! # Uniform polynomial spectral complexity of invariant canonical channel outputs

The exact combined-factor equivalence transports the concrete output density
to the project's invariant tensor algebra. No untracked coordinate shuffle
or polynomial eigenvalue-count assumption is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.TensorChannelCovariance
open Matrix TensorPower TensorPermutation ChannelPowerReindex ChannelEntropy CovariantOptimization
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n m : ℕ}

@[simp] theorem indexProdEquiv_fst_coordinates (k : ℕ) (x : Index (Fin n × Fin m) k) (l : Fin k) :
    indexEquiv (Fin n) k ((indexProdEquiv (Fin n) (Fin m) k x).1) l =
      (indexEquiv (Fin n × Fin m) k x l).1 := by
  simp [indexProdEquiv, Equiv.arrowProdEquivProdArrow]

@[simp] theorem indexProdEquiv_snd_coordinates (k : ℕ) (x : Index (Fin n × Fin m) k) (l : Fin k) :
    indexEquiv (Fin m) k ((indexProdEquiv (Fin n) (Fin m) k x).2) l =
      (indexEquiv (Fin n × Fin m) k x l).2 := by
  simp [indexProdEquiv, Equiv.arrowProdEquivProdArrow]

theorem indexProdEquiv_factorPermutation (k : ℕ) (p : Equiv.Perm (Fin k)) (x : Index (Fin n × Fin m) k) :
    indexProdEquiv (Fin n) (Fin m) k (factorPermutation (Fin n × Fin m) k p x) =
      (factorPermutation (Fin n) k p (indexProdEquiv (Fin n) (Fin m) k x).1,
        factorPermutation (Fin m) k p (indexProdEquiv (Fin n) (Fin m) k x).2) := by
  apply Prod.ext
  · apply (indexEquiv (Fin n) k).injective
    funext l
    simp
  · apply (indexEquiv (Fin m) k).injective
    funext l
    simp

def outputIndexEquiv (n m k : ℕ) : Index (Fin n × Fin m) k ≃ Fin (n ^ k * m ^ k) :=
  (indexProdEquiv (Fin n) (Fin m) k).trans
    (((channelIndexEquiv n k).prodCongr (channelIndexEquiv m k)).trans finProdFinEquiv)

theorem outputIndexEquiv_factorPermutation (k : ℕ) (p : Equiv.Perm (Fin k)) (x : Index (Fin n × Fin m) k) :
    outputIndexEquiv n m k (factorPermutation (Fin n × Fin m) k p x) =
      outputReindex (channelPermutation n k p) (channelPermutation m k p) (outputIndexEquiv n m k x) := by
  simp only [outputIndexEquiv, Equiv.trans_apply, indexProdEquiv_factorPermutation,
    Equiv.prodCongr_apply, Prod.map, outputReindex, Equiv.symm_apply_apply, channelPermutation_apply]
  rfl

theorem outputIndexEquiv_symm_factorPermutation (k : ℕ) (p : Equiv.Perm (Fin k)) (x : Index (Fin n × Fin m) k) :
    outputIndexEquiv n m k ((factorPermutation (Fin n × Fin m) k p).symm x) =
      (outputReindex (channelPermutation n k p) (channelPermutation m k p)).symm (outputIndexEquiv n m k x) := by
  apply (outputReindex (channelPermutation n k p) (channelPermutation m k p)).injective
  rw [← outputIndexEquiv_factorPermutation, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The actual canonical output transported into the literal invariant tensor algebra. -/
def invariantOutput (Φ : KrausChannel n m) (k : ℕ)
    (ω : InvariantDensity (channelPermutation n k)) : invariantAlgebra (Fin n × Fin m) k := by
  let σ := pureOutput (Φ.tensorPower k) (TestingPrimal.densityInput ω.val)
  refine ⟨Matrix.reindex (outputIndexEquiv n m k).symm (outputIndexEquiv n m k).symm σ.matrix, ?_⟩
  intro p
  have hs := congrArg State.matrix (canonicalOutput_tensorPower_invariant Φ k ω p)
  change Matrix.reindex (outputReindex (channelPermutation n k p) (channelPermutation m k p))
    (outputReindex (channelPermutation n k p) (channelPermutation m k p)) σ.matrix = σ.matrix at hs
  ext i j
  change σ.matrix (outputIndexEquiv n m k ((factorPermutation (Fin n × Fin m) k p).symm i))
    (outputIndexEquiv n m k ((factorPermutation (Fin n × Fin m) k p).symm j)) =
      σ.matrix (outputIndexEquiv n m k i) (outputIndexEquiv n m k j)
  rw [outputIndexEquiv_symm_factorPermutation, outputIndexEquiv_symm_factorPermutation]
  exact congrFun (congrFun hs (outputIndexEquiv n m k i)) (outputIndexEquiv n m k j)

/-- The invariant-output representative has exactly the same spectrum as the physical output state. -/
theorem invariantOutput_spectrum (Φ : KrausChannel n m) (k : ℕ)
    (ω : InvariantDensity (channelPermutation n k)) :
    spectrum ℂ (invariantOutput Φ k ω).val =
      spectrum ℂ (pureOutput (Φ.tensorPower k) (TestingPrimal.densityInput ω.val)).matrix := by
  change spectrum ℂ ((Matrix.reindexAlgEquiv ℂ ℂ (outputIndexEquiv n m k).symm)
    (pureOutput (Φ.tensorPower k) (TestingPrimal.densityInput ω.val)).matrix) = _
  exact AlgEquiv.spectrum_eq _ _

/-- Uniform polynomial bound on the actual alternative-output spectrum for every invariant optimizer. -/
theorem canonical_output_spectrum_card_le (Φ : KrausChannel n m) (k : ℕ)
    (ω : InvariantDensity (channelPermutation n k)) :
    (spectrum ℂ (pureOutput (Φ.tensorPower k) (TestingPrimal.densityInput ω.val)).matrix).ncard ≤
      (k + 1) ^ ((n * m) * (n * m)) := by
  rw [← invariantOutput_spectrum Φ k ω]
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    ncard_spectrum_invariant_le k (invariantOutput Φ k ω)

end QuantumChannelStein.TensorChannelCovariance
