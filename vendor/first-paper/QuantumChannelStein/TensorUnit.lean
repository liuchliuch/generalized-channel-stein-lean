import QuantumChannelStein.TensorDomination

/-! # The one-use identity for concrete channel powers -/
noncomputable section
namespace QuantumChannelStein
open scoped Kronecker
open Matrix

/-- Flattening a tensor product with a one-dimensional scalar identity changes
no matrix entries after the numerical dimension transport. -/
theorem reindex_tensor_one {n : ℕ} (X : Operator n) :
    Matrix.reindex (finCongr (Nat.mul_one n)) (finCongr (Nat.mul_one n))
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ (1 : Operator 1))) = X := by
  ext i j
  simp [Matrix.reindex_apply, finProdFinEquiv, Matrix.one_apply]
  split_ifs with h
  · congr 1 <;> apply Fin.ext <;> simp [Fin.divNat]
  · exfalso
    apply h
    apply Fin.ext
    simp [Fin.modNat]

namespace KrausChannel
variable {n m : ℕ}

theorem cast_apply {n' m' : ℕ} (Φ : KrausChannel n m) (hn : n = n') (hm : m = m')
    (X : Operator n) :
    (Φ.cast hn hm).apply (Matrix.reindex (finCongr hn) (finCongr hn) X) =
      Matrix.reindex (finCongr hm) (finCongr hm) (Φ.apply X) := by
  cases hn
  cases hm
  simp [cast, Matrix.reindex_apply]

/-- Tensoring with the one-dimensional identity channel has the original action. -/
theorem tensor_identity_cast_apply (Φ : KrausChannel n m) (X : Operator n) :
    ((tensor Φ (identity 1)).cast (Nat.mul_one n) (Nat.mul_one m)).apply X = Φ.apply X := by
  let Xin := Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ (1 : Operator 1))
  have h := cast_apply (tensor Φ (identity 1)) (Nat.mul_one n) (Nat.mul_one m) Xin
  change ((tensor Φ (identity 1)).cast (Nat.mul_one n) (Nat.mul_one m)).apply
    (Matrix.reindex (finCongr (Nat.mul_one n)) (finCongr (Nat.mul_one n))
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ (1 : Operator 1)))) =
    Matrix.reindex (finCongr (Nat.mul_one m)) (finCongr (Nat.mul_one m))
      ((tensor Φ (identity 1)).apply (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (X ⊗ₖ (1 : Operator 1)))) at h
  rw [reindex_tensor_one, tensor_apply_product, identity_apply, reindex_tensor_one] at h
  exact h

@[simp] theorem cast_cast {n' m' n'' m'' : ℕ} (Φ : KrausChannel n m)
    (hn : n = n') (hm : m = m') (hn' : n' = n'') (hm' : m' = m'') :
    (Φ.cast hn hm).cast hn' hm' = Φ.cast (hn.trans hn') (hm.trans hm') := by
  cases hn; cases hm; cases hn'; cases hm'; rfl

/-- One independent channel use is the original complex-linear map. -/
theorem tensorPower_one_toLinearMap (Φ : KrausChannel n m) :
    ((tensorPower Φ 1).cast (Nat.pow_one n) (Nat.pow_one m)).toLinearMap = Φ.toLinearMap := by
  ext X i j
  have h := tensor_identity_cast_apply Φ X
  simpa only [tensorPower, cast_cast, KrausChannel.toLinearMap] using congrFun (congrFun h i) j

end KrausChannel
end QuantumChannelStein
