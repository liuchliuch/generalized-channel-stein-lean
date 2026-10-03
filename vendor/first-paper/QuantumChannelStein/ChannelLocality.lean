import QuantumChannelStein.OperationalTesting
import QuantumChannelStein.TensorMap

/-! # Actual local channel actions and their commuting reference extensions -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ChannelLocality
open Matrix ChannelEntropy OperationalTesting
open scoped BigOperators Kronecker ComplexOrder
variable {r s n m : ℕ}

theorem tensor_apply_reindex (Γ : KrausChannel r s) (Φ : KrausChannel n m)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    (Γ.tensor Φ).apply (Matrix.reindex finProdFinEquiv finProdFinEquiv X) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (∑ i : Fin Γ.rank, ∑ j : Fin Φ.rank,
          (Γ.kraus i ⊗ₖ Φ.kraus j) * X * (Γ.kraus i ⊗ₖ Φ.kraus j)ᴴ) := by
  unfold KrausChannel.apply
  change (∑ k : Fin (Γ.rank * Φ.rank),
    Matrix.reindex finProdFinEquiv finProdFinEquiv (KrausChannel.tensorKraus Γ Φ (finProdFinEquiv.symm k)) *
      Matrix.reindex finProdFinEquiv finProdFinEquiv X *
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (KrausChannel.tensorKraus Γ Φ (finProdFinEquiv.symm k)))ᴴ) = _
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Matrix.conjTranspose_reindex]
  change (∑ k : Fin Γ.rank × Fin Φ.rank,
    Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (KrausChannel.tensorKraus Γ Φ k) *
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv X *
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (KrausChannel.tensorKraus Γ Φ k)ᴴ) = _
  simp_rw [Matrix.reindexLinearEquiv_mul]
  rw [← map_sum]
  simp only [Fintype.sum_prod_type, KrausChannel.tensorKraus, Matrix.reindexLinearEquiv_apply]

theorem identity_tensor_apply_reindex (Φ : KrausChannel n m) (r : ℕ)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    ((KrausChannel.identity r).tensor Φ).apply (Matrix.reindex finProdFinEquiv finProdFinEquiv X) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Φ.amplify r X) := by
  rw [tensor_apply_reindex]
  simp only [KrausChannel.identity, Fin.sum_univ_one, KrausChannel.amplify]

/-- The existing operational mixed-output definition is the actual normalized tensor channel. -/
theorem outputState_eq_tensor (Φ : KrausChannel n m) (r : ℕ) (ρ : State (r * n)) :
    outputState Φ r ρ = ((KrausChannel.identity r).tensor Φ).onState ρ := by
  apply state_eq_of_matrix_eq
  change Matrix.reindex _ _ (Φ.amplify r (Matrix.reindex _ _ ρ.matrix)) = _
  rw [← identity_tensor_apply_reindex]
  congr 1
  ext i j
  change ρ.matrix (finProdFinEquiv (finProdFinEquiv.symm i))
    (finProdFinEquiv (finProdFinEquiv.symm j)) = ρ.matrix i j
  simp only [Equiv.apply_symm_apply]

/-- Reference recovery and system evolution commute as literal matrix maps. -/
theorem local_channels_commute (Γ : KrausChannel r s) (Φ : KrausChannel n m) :
    ((Γ.tensor (KrausChannel.identity m)).toLinearMap).comp
        (((KrausChannel.identity r).tensor Φ).toLinearMap) =
    (((KrausChannel.identity s).tensor Φ).toLinearMap).comp
        ((Γ.tensor (KrausChannel.identity n)).toLinearMap) := by
  apply MatrixMap.choi_injective
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i,a⟩,rfl⟩ := (finProdFinEquiv (m := r) (n := n)).surjective i
  obtain ⟨⟨j,b⟩,rfl⟩ := (finProdFinEquiv (m := r) (n := n)).surjective j
  simp only [MatrixMap.choi, LinearMap.comp_apply, KrausChannel.toLinearMap]
  rw [← MatrixMap.reindex_product_single]
  change (Γ.tensor (KrausChannel.identity m)).apply
    (((KrausChannel.identity r).tensor Φ).apply
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.single i j 1 ⊗ₖ Matrix.single a b 1))) u v =
    ((KrausChannel.identity s).tensor Φ).apply
    ((Γ.tensor (KrausChannel.identity n)).apply
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.single i j 1 ⊗ₖ Matrix.single a b 1))) u v
  simp only [KrausChannel.tensor_apply_product, KrausChannel.identity_apply]

/-- State-level commuting square used to transport a recovery channel through either hypothesis. -/
theorem reference_recovery_output (Γ : KrausChannel r s) (Φ : KrausChannel n m)
    (ρ : State (r * n)) :
    (Γ.tensor (KrausChannel.identity m)).onState (outputState Φ r ρ) =
      outputState Φ s ((Γ.tensor (KrausChannel.identity n)).onState ρ) := by
  rw [outputState_eq_tensor, outputState_eq_tensor]
  apply state_eq_of_matrix_eq
  exact congrArg (fun f : MatrixMap (r * n) (s * m) => f ρ.matrix) (local_channels_commute Γ Φ)

end QuantumChannelStein.ChannelLocality
