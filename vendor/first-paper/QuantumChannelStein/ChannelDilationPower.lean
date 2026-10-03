import QuantumChannelStein.ChannelPowerReindex
import QuantumChannelStein.TensorBlockReindex
import QuantumChannelStein.ExactComparison

/-!
# Prescribed dilation tensors are dilations of actual channel powers

The coordinate equivalences match the concrete recursive Kraus channel
powers. Environment spaces are exactly the tensor powers of the prescribed
spaces. Norms, isometries, channel actions, and auxiliary errors are preserved
by proved finite reindexings.
-/
noncomputable section
namespace QuantumChannelStein.ChannelDilationPower
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix TensorPower ChannelPowerReindex EnvironmentTensor TensorBlockReindex UniformApproximation

/-- Repeated input/output Choi pairs in the concrete channel-power convention. -/
def channelChoiEquiv (a b k : ℕ) :
    Index (Fin a × Fin b) k ≃ Fin (a ^ k) × Fin (b ^ k) :=
  (indexProdEquiv (Fin a) (Fin b) k).trans
    (Equiv.prodCongr (channelIndexEquiv a k) (channelIndexEquiv b k))

@[simp] theorem channelChoiEquiv_symm_apply (a b k : ℕ)
    (i : Index (Fin a) k) (j : Index (Fin b) k) :
    (channelChoiEquiv a b k).symm (channelIndexEquiv a k i, channelIndexEquiv b k j) =
      (indexProdEquiv (Fin a) (Fin b) k).symm (i, j) := by
  change (indexProdEquiv (Fin a) (Fin b) k).symm
    ((channelIndexEquiv a k).symm (channelIndexEquiv a k i),
      (channelIndexEquiv b k).symm (channelIndexEquiv b k j)) = _
  simp only [Equiv.symm_apply_apply]

/-- The actual power channel has precisely the reindexed tensor-power Choi matrix. -/
theorem choi_tensorPower_reindex {a b : ℕ} (Φ : KrausChannel a b) (k : ℕ) :
    (KrausChannel.tensorPower Φ k).choi =
      Matrix.reindex (channelChoiEquiv a b k) (channelChoiEquiv a b k)
        (TensorPower.tensorPower Φ.choi k) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  obtain ⟨i, rfl⟩ := (channelIndexEquiv a k).surjective i
  obtain ⟨j, rfl⟩ := (channelIndexEquiv a k).surjective j
  obtain ⟨x, rfl⟩ := (channelIndexEquiv b k).surjective x
  obtain ⟨y, rfl⟩ := (channelIndexEquiv b k).surjective y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, channelChoiEquiv_symm_apply,
    tensorPower_apply_eq_prod, indexEquiv_indexProdEquiv_symm, choi_tensorPower_apply]

/-- A prescribed dilation tensor on the concrete finite-dimensional channel coordinates. -/
def powerDilation {a b e : ℕ} (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (k : ℕ) :
    Matrix (Fin (b ^ k) × Fin (e ^ k)) (Fin (a ^ k)) ℂ :=
  Matrix.reindex (Equiv.prodCongr (channelIndexEquiv b k) (channelIndexEquiv e k))
    (channelIndexEquiv a k) (blockDilation V k)

@[simp] theorem powerDilation_apply {a b e : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (k : ℕ)
    (i : Index (Fin b) k) (j : Index (Fin e) k) (x : Index (Fin a) k) :
    powerDilation V k (channelIndexEquiv b k i, channelIndexEquiv e k j)
      (channelIndexEquiv a k x) =
      ∏ l : Fin k, V (indexEquiv (Fin b) k i l, indexEquiv (Fin e) k j l)
        (indexEquiv (Fin a) k x l) := by
  simp only [powerDilation, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_apply_apply,
    blockDilation_apply_eq_prod]

/-- Reindexing preserves the actual Hilbert operator norm of a dilation tensor. -/
theorem norm_powerDilation {a b e : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (k : ℕ) :
    ‖powerDilation V k‖ = ‖TensorPower.tensorPower V k‖ := by
  rw [powerDilation, norm_reindex, norm_blockDilation]

/-- Isometry is invariant under independent input/output coordinate equivalences. -/
theorem reindex_isometry {r s r' s' : Type*}
    [Fintype r] [Fintype s] [Fintype r'] [Fintype s']
    [DecidableEq r] [DecidableEq s] [DecidableEq r'] [DecidableEq s']
    (er : r ≃ r') (es : s ≃ s') (V : Matrix r s ℂ) (hV : Vᴴ * V = 1) :
    (Matrix.reindex er es V)ᴴ * Matrix.reindex er es V = 1 := by
  rw [Matrix.conjTranspose_reindex]
  change (Matrix.reindexLinearEquiv ℂ ℂ es er Vᴴ) *
    (Matrix.reindexLinearEquiv ℂ ℂ er es V) = _
  rw [Matrix.reindexLinearEquiv_mul, hV, Matrix.reindexLinearEquiv_one]

/-- Tensoring a prescribed isometry gives an actual isometry in the
concrete channel-power spaces, including the zeroth identity. -/
theorem powerDilation_isometry {a b e : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ * V = 1) (k : ℕ) :
    (powerDilation V k)ᴴ * powerDilation V k = 1 := by
  apply reindex_isometry
  exact reindex_isometry (indexProdEquiv (Fin b) (Fin e) k) (Equiv.refl _)
    (TensorPower.tensorPower V k) (tensorPower_isometry V hV k)

/-- The vectorized column matrix of a prescribed dilation tensor is the
actual column tensor power with the same canonical Choi coordinates. -/
theorem dilationColumns_powerDilation {a b e : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (k : ℕ) :
    dilationColumns (powerDilation V k) =
      Matrix.reindex (channelChoiEquiv a b k) (channelIndexEquiv e k)
        (TensorPower.tensorPower (dilationColumns V) k) := by
  ext ⟨i, j⟩ x
  obtain ⟨i, rfl⟩ := (channelIndexEquiv a k).surjective i
  obtain ⟨j, rfl⟩ := (channelIndexEquiv b k).surjective j
  obtain ⟨x, rfl⟩ := (channelIndexEquiv e k).surjective x
  change powerDilation V k _ _ = _
  simp only [powerDilation_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    channelChoiEquiv_symm_apply, Equiv.symm_apply_apply, tensorPower_apply_eq_prod,
    indexEquiv_indexProdEquiv_symm, dilationColumns]

/-- The prescribed tensor dilation's Choi Gram operator is the genuine
reindexed tensor power of the one-use Choi Gram operator. -/
theorem columns_gram_powerDilation {a b e : ℕ}
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (k : ℕ) :
    dilationColumns (powerDilation V k) * (dilationColumns (powerDilation V k))ᴴ =
      Matrix.reindex (channelChoiEquiv a b k) (channelChoiEquiv a b k)
        (TensorPower.tensorPower (dilationColumns V * (dilationColumns V)ᴴ) k) := by
  rw [dilationColumns_powerDilation, Matrix.conjTranspose_reindex]
  change (Matrix.reindexLinearEquiv ℂ ℂ (channelChoiEquiv a b k) (channelIndexEquiv e k)
    (TensorPower.tensorPower (dilationColumns V) k)) *
    (Matrix.reindexLinearEquiv ℂ ℂ (channelIndexEquiv e k) (channelChoiEquiv a b k)
      (TensorPower.tensorPower (dilationColumns V) k)ᴴ) = _
  rw [Matrix.reindexLinearEquiv_mul, ← tensorPower_conjTranspose, ← tensorPower_mul]
  rfl

/-- The prescribed tensor dilation represents the actual recursively
constructed channel power, as equality of the complex-linear maps. -/
theorem dilationMap_powerDilation {a b e : ℕ} (Φ : KrausChannel a b)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : dilationMap V = Φ.toLinearMap) (k : ℕ) :
    dilationMap (powerDilation V k) = (KrausChannel.tensorPower Φ k).toLinearMap := by
  apply MatrixMap.choi_injective
  rw [choi_dilationMap, columns_gram_powerDilation, ← choi_dilationMap, hV,
    MatrixMap.choi_toLinearMap, ← choi_tensorPower_reindex, MatrixMap.choi_toLinearMap]

/-- Flatten an auxiliary matrix to the concrete finite environment powers. -/
def finiteAuxiliary {e f : ℕ} (k : ℕ)
    (C : Matrix (Index (Fin e) k) (Index (Fin f) k) ℂ) :
    Matrix (Fin (e ^ k)) (Fin (f ^ k)) ℂ :=
  Matrix.reindex (channelIndexEquiv e k) (channelIndexEquiv f k) C

/-- Return an auxiliary matrix to the recursive tensor coordinates. -/
def indexedAuxiliary {e f : ℕ} (k : ℕ)
    (C : Matrix (Fin (e ^ k)) (Fin (f ^ k)) ℂ) :
    Matrix (Index (Fin e) k) (Index (Fin f) k) ℂ :=
  Matrix.reindex (channelIndexEquiv e k).symm (channelIndexEquiv f k).symm C

@[simp] theorem finiteAuxiliary_indexedAuxiliary {e f : ℕ} (k : ℕ)
    (C : Matrix (Fin (e ^ k)) (Fin (f ^ k)) ℂ) :
    finiteAuxiliary k (indexedAuxiliary k C) = C := by
  ext i j
  simp only [finiteAuxiliary, indexedAuxiliary, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

@[simp] theorem norm_finiteAuxiliary {e f : ℕ} (k : ℕ)
    (C : Matrix (Index (Fin e) k) (Index (Fin f) k) ℂ) : ‖finiteAuxiliary k C‖ = ‖C‖ :=
  norm_reindex _ _ _

@[simp] theorem norm_indexedAuxiliary {e f : ℕ} (k : ℕ)
    (C : Matrix (Fin (e ^ k)) (Fin (f ^ k)) ℂ) : ‖indexedAuxiliary k C‖ = ‖C‖ :=
  norm_reindex _ _ _

/-- Environmental application commutes with the actual finite coordinate flattening. -/
theorem finiteAuxiliary_environment {a b e f : ℕ}
    (V : Matrix (Fin b × Fin f) (Fin a) ℂ) (k : ℕ)
    (C : Matrix (Index (Fin e) k) (Index (Fin f) k) ℂ) :
    Matrix.reindex
      (Equiv.prodCongr (channelIndexEquiv b k) (channelIndexEquiv e k)) (channelIndexEquiv a k)
      (applyEnvironment (blockDilation V k) C) =
      applyEnvironment (powerDilation V k) (finiteAuxiliary k C) :=
  applyEnvironment_reindex (channelIndexEquiv a k) (channelIndexEquiv b k)
    (channelIndexEquiv e k) (channelIndexEquiv f k) (blockDilation V k) C

/-- The actual error is identical in recursive and concrete finite coordinates. -/
theorem finiteAuxiliary_error {a b e f : ℕ}
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (V : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (k : ℕ) (C : Matrix (Index (Fin e) k) (Index (Fin f) k) ℂ) :
    ‖powerDilation U k - applyEnvironment (powerDilation V k) (finiteAuxiliary k C)‖ =
      auxiliaryError U V k C := by
  rw [← finiteAuxiliary_environment]
  change ‖Matrix.reindex
    (Equiv.prodCongr (channelIndexEquiv b k) (channelIndexEquiv e k)) (channelIndexEquiv a k)
    (blockDilation U k - applyEnvironment (blockDilation V k) C)‖ = _
  rw [norm_reindex]
  rfl

theorem indexedAuxiliary_error {a b e f : ℕ}
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (V : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (k : ℕ) (C : Matrix (Fin (e ^ k)) (Fin (f ^ k)) ℂ) :
    auxiliaryError U V k (indexedAuxiliary k C) =
      ‖powerDilation U k - applyEnvironment (powerDilation V k) C‖ := by
  have h := finiteAuxiliary_error U V k (indexedAuxiliary k C)
  rw [finiteAuxiliary_indexedAuxiliary] at h
  exact h.symm

end QuantumChannelStein.ChannelDilationPower
