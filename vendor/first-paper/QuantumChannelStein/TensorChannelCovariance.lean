import QuantumChannelStein.CovariantOptimization
import QuantumChannelStein.TensorPermutation

/-! # Actual tensor-power covariance and invariant channel optimizers

The symmetric-group representation is transported through the channel's
proved recursive index equivalence. Choi product entries prove covariance
of the literal Kraus tensor powers, without assuming a tensor oracle.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.TensorChannelCovariance
open Matrix TensorPower TensorPermutation ChannelPowerReindex ChannelEntropy
  CovariantOrbitRecovery CovariantOptimization DivergenceOptimization
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n m : ℕ}

def channelPermutation (d k : ℕ) : Equiv.Perm (Fin k) →* Equiv.Perm (Fin (d ^ k)) where
  toFun p := (channelIndexEquiv d k).symm.trans
    ((factorPermutation (Fin d) k p).trans (channelIndexEquiv d k))
  map_one' := by
    ext x
    simp only [factorPermutation_one, Equiv.trans_apply, Equiv.Perm.one_apply, Equiv.apply_symm_apply]
  map_mul' p q := by
    ext x
    simp only [factorPermutation_mul, Equiv.trans_apply, Equiv.Perm.mul_apply, Equiv.symm_apply_apply]

@[simp] theorem channelPermutation_apply (d k : ℕ) (p : Equiv.Perm (Fin k)) (i : Index (Fin d) k) :
    channelPermutation d k p (channelIndexEquiv d k i) =
      channelIndexEquiv d k (factorPermutation (Fin d) k p i) := by
  simp [channelPermutation]

@[simp] theorem channelPermutation_symm_apply (d k : ℕ) (p : Equiv.Perm (Fin k)) (i : Index (Fin d) k) :
    (channelPermutation d k p).symm (channelIndexEquiv d k i) =
      channelIndexEquiv d k ((factorPermutation (Fin d) k p).symm i) := by
  simp [channelPermutation]

/-- Simultaneous tensor-factor permutations preserve the actual repeated-channel Choi matrix. -/
theorem choi_tensorPower_invariant (Φ : KrausChannel n m) (k : ℕ) (p : Equiv.Perm (Fin k)) :
    Matrix.reindex ((channelPermutation n k p).prodCongr (channelPermutation m k p))
      ((channelPermutation n k p).prodCongr (channelPermutation m k p)) (Φ.tensorPower k).choi =
      (Φ.tensorPower k).choi := by
  ext ⟨i,a⟩ ⟨j,b⟩
  obtain ⟨i,rfl⟩ := (channelIndexEquiv n k).surjective i
  obtain ⟨j,rfl⟩ := (channelIndexEquiv n k).surjective j
  obtain ⟨a,rfl⟩ := (channelIndexEquiv m k).surjective a
  obtain ⟨b,rfl⟩ := (channelIndexEquiv m k).surjective b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map, channelPermutation_symm_apply, choi_tensorPower_apply,
    factorPermutation_symm_coordinates]
  exact Equiv.prod_comp p (fun l => Φ.choi
    (indexEquiv (Fin n) k i l, indexEquiv (Fin m) k a l)
    (indexEquiv (Fin n) k j l, indexEquiv (Fin m) k b l))

/-- The literal Kraus channel powers satisfy the required common permutation covariance. -/
theorem tensorPower_covariant (Φ : KrausChannel n m) (k : ℕ) :
    Covariant (channelPermutation n k) (channelPermutation m k) (Φ.tensorPower k) := by
  intro p X
  have hf : (reindexChannel (channelPermutation n k p) (channelPermutation m k p)
      (Φ.tensorPower k)).toLinearMap = (Φ.tensorPower k).toLinearMap := by
    apply MatrixMap.choi_injective
    simp only [MatrixMap.choi_toLinearMap, reindexChannel_choi]
    exact choi_tensorPower_invariant Φ k p
  have h := reindexChannel_apply (channelPermutation n k p) (channelPermutation m k p) (Φ.tensorPower k) X
  change (reindexChannel (channelPermutation n k p) (channelPermutation m k p)
    (Φ.tensorPower k)).toLinearMap _ = _ at h
  rw [hf] at h
  exact h

/-- The exact optimization reduction needed in the tensor-channel version of Fawzi--Fawzi Lemma 4.4. -/
theorem channelValue_tensorPower_eq_invariant_density_sup (D : StateDivergence) (hD : DataProcessing D)
    (Φ Ψ : KrausChannel n m) (k : ℕ) :
    channelValue D (Φ.tensorPower k) (Ψ.tensorPower k) =
      ⨆ ω : InvariantDensity (channelPermutation n k),
        D (pureOutput (Φ.tensorPower k) (TestingPrimal.densityInput ω.val))
          (pureOutput (Ψ.tensorPower k) (TestingPrimal.densityInput ω.val)) :=
  channelValue_eq_invariant_density_sup D hD _ _ _ _ (tensorPower_covariant Φ k) (tensorPower_covariant Ψ k)

theorem sharp_tensorPower_eq_invariant_density_sup (α : ℝ) (hα : 1 < α)
    (Φ Ψ : KrausChannel n m) (k : ℕ) :
    channelValue (fun ρ σ => SharpDivergence.divergence α hα ρ σ) (Φ.tensorPower k) (Ψ.tensorPower k) =
      ⨆ ω : InvariantDensity (channelPermutation n k), SharpDivergence.divergence α hα
        (pureOutput (Φ.tensorPower k) (TestingPrimal.densityInput ω.val))
          (pureOutput (Ψ.tensorPower k) (TestingPrimal.densityInput ω.val)) :=
  channelValue_tensorPower_eq_invariant_density_sup (fun ρ σ => SharpDivergence.divergence α hα ρ σ)
    (fun Φ ρ σ => SharpDivergence.divergence_data_processing α hα Φ ρ σ) Φ Ψ k

theorem renyi_tensorPower_eq_invariant_density_sup (α : ℝ) (hα : 1 < α)
    (Φ Ψ : KrausChannel n m) (k : ℕ) :
    ChannelRenyi.channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k) =
      ⨆ ω : InvariantDensity (channelPermutation n k), SandwichedRenyi.renyi α hα
        (pureOutput (Φ.tensorPower k) (TestingPrimal.densityInput ω.val))
          (pureOutput (Ψ.tensorPower k) (TestingPrimal.densityInput ω.val)) :=
  channelValue_tensorPower_eq_invariant_density_sup (fun ρ σ => SandwichedRenyi.renyi α hα ρ σ)
    (fun Φ ρ σ => SandwichedRenyi.renyi_data_processing α hα Φ ρ σ) Φ Ψ k

end QuantumChannelStein.TensorChannelCovariance
