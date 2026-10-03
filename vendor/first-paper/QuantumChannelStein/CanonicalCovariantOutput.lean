import QuantumChannelStein.TensorChannelCovariance
import QuantumChannelStein.ChannelEntropySuperadditive
import QuantumChannelStein.SandwichedRenyiTensor

/-! # Actual invariance of the canonical weighted-Choi output states -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.CovariantOptimization
open Matrix ChannelEntropy ChannelPowerReindex CovariantOrbitRecovery
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {G : Type*} [Fintype G] [Group G] [DecidableEq G] {n m : ℕ}

theorem sqrt_reindex (e : Fin n ≃ Fin m) (A : Operator n) (hA : A.PosSemidef) :
    CFC.sqrt (Matrix.reindex e e A) = Matrix.reindex e e (CFC.sqrt A) := by
  simpa only [CFC.sqrt_eq_rpow, CFC.rpow_eq_pow] using
    SandwichedRenyi.rpow_reindex e A hA (1 / 2)

theorem canonicalInput_invariant (e : Equiv.Perm (Fin n)) (ω : State n)
    (hω : Matrix.reindex e e ω.matrix = ω.matrix) :
    reindexInput e (TestingPrimal.densityInput ω) = TestingPrimal.densityInput ω := by
  have hs : Matrix.reindex e e (CFC.sqrt ω.matrix) = CFC.sqrt ω.matrix := by
    rw [← sqrt_reindex e ω.matrix ω.positive, hω]
  apply Subtype.ext
  ext ⟨i,j⟩
  exact congrFun (congrFun hs i) j

theorem reindexChannel_eq_of_covariant
    (p : G →* Equiv.Perm (Fin n)) (q : G →* Equiv.Perm (Fin m))
    (Φ : KrausChannel n m) (hΦ : Covariant p q Φ) (g : G) :
    (reindexChannel (p g) (q g) Φ).toLinearMap = Φ.toLinearMap := by
  ext X i j
  obtain ⟨Y, rfl⟩ := (Matrix.reindexAlgEquiv ℂ ℂ (p g)).surjective X
  change (reindexChannel (p g) (q g) Φ).apply (Matrix.reindex (p g) (p g) Y) i j =
    Φ.apply (Matrix.reindex (p g) (p g) Y) i j
  rw [reindexChannel_apply, hΦ g]

/-- An invariant canonical density produces an invariant actual output density. -/
theorem canonicalOutput_invariant
    (p : G →* Equiv.Perm (Fin n)) (q : G →* Equiv.Perm (Fin m))
    (Φ : KrausChannel n m) (hΦ : Covariant p q Φ) (ω : InvariantDensity p) (g : G) :
    (pureOutput Φ (TestingPrimal.densityInput ω.val)).reindex (outputReindex (p g) (q g)) =
      pureOutput Φ (TestingPrimal.densityInput ω.val) := by
  have h := pureOutput_reindexChannel (p g) (q g) Φ (TestingPrimal.densityInput ω.val)
  rw [canonicalInput_invariant _ _ (ω.property g),
    pureOutput_congr _ _ (reindexChannel_eq_of_covariant p q Φ hΦ g)] at h
  exact h.symm

/-- Tensor-power specialization with the precise flattened reference/output permutation. -/
theorem canonicalOutput_tensorPower_invariant (Φ : KrausChannel n m) (k : ℕ)
    (ω : InvariantDensity (TensorChannelCovariance.channelPermutation n k)) (g : Equiv.Perm (Fin k)) :
    (pureOutput (Φ.tensorPower k) (TestingPrimal.densityInput ω.val)).reindex
      (outputReindex (TensorChannelCovariance.channelPermutation n k g)
        (TensorChannelCovariance.channelPermutation m k g)) =
      pureOutput (Φ.tensorPower k) (TestingPrimal.densityInput ω.val) :=
  canonicalOutput_invariant _ _ _ (TensorChannelCovariance.tensorPower_covariant Φ k) ω g

end QuantumChannelStein.CovariantOptimization
