import QuantumChannelStein.EnvironmentTensor
import QuantumChannelStein.UniformApproximation

/-!
# Canonical fixed-block and padding identities for dilation tensors

All identities concern actual rectangular matrices. They preserve the
relative order of blocks and factors, including empty blocks and scalar
zeroth tensor powers.
-/
noncomputable section
namespace QuantumChannelStein.TensorBlockReindex
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix TensorPower EnvironmentTensor

/-- Coordinate formula for a tensor dilation with its output and environment
groups separated. -/
theorem blockDilation_apply_eq_prod {a b f : Type*} (V : Matrix (b × f) a ℂ)
    (k : ℕ) (i : Index b k) (e : Index f k) (j : Index a k) :
    blockDilation V k (i, e) j = ∏ l : Fin k,
      V (indexEquiv b k i l, indexEquiv f k e l) (indexEquiv a k j l) := by
  simp only [blockDilation, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.refl_symm, Equiv.refl_apply, tensorPower_apply_eq_prod,
    indexEquiv_indexProdEquiv_symm]

/-- Regrouping nested dilation tensors gives precisely the dilation tensor
at the product blocklength. -/
theorem blockDilation_mul_reindex {a b f : Type*} (V : Matrix (b × f) a ℂ)
    (k m : ℕ) :
    Matrix.reindex
      (Equiv.prodCongr (indexMulEquiv b k m) (indexMulEquiv f k m))
      (indexMulEquiv a k m) (blockDilation (blockDilation V k) m) =
        blockDilation V (k * m) := by
  ext ⟨i, e⟩ j
  obtain ⟨i, rfl⟩ := (indexMulEquiv b k m).surjective i
  obtain ⟨e, rfl⟩ := (indexMulEquiv f k m).surjective e
  obtain ⟨j, rfl⟩ := (indexMulEquiv a k m).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_apply_apply, blockDilation_apply_eq_prod]
  rw [← (blockIndexEquiv k m).prod_comp
    (fun l => V (indexEquiv b (k * m) (indexMulEquiv b k m i) l,
      indexEquiv f (k * m) (indexMulEquiv f k m e) l)
        (indexEquiv a (k * m) (indexMulEquiv a k m j) l)), Fintype.prod_prod_type]
  simp only [indexEquiv_indexMulEquiv]

/-- Regroup outputs and environments from two consecutive dilation blocks. -/
def blockAddEquiv (b f : Type*) (p q : ℕ) :
    (Index b p × Index f p) × (Index b q × Index f q) ≃
      Index b (p + q) × Index f (p + q) :=
  (Equiv.prodProdProdComm (Index b p) (Index f p) (Index b q) (Index f q)).trans
    (Equiv.prodCongr (indexAddEquiv b p q) (indexAddEquiv f p q))

@[simp] theorem blockAddEquiv_apply (b f : Type*) (p q : ℕ)
    (i : Index b p) (e : Index f p) (j : Index b q) (d : Index f q) :
    blockAddEquiv b f p q ((i, e), (j, d)) =
      (indexAddEquiv b p q (i, j), indexAddEquiv f p q (e, d)) := rfl

/-- Padding a dilation block by the residual exact tensor block gives the
actual dilation tensor at the sum blocklength. -/
theorem blockDilation_add_reindex {a b f : Type*} (V : Matrix (b × f) a ℂ)
    (p q : ℕ) :
    Matrix.reindex (blockAddEquiv b f p q) (indexAddEquiv a p q)
      (blockDilation V p ⊗ₖ blockDilation V q) = blockDilation V (p + q) := by
  ext i j
  obtain ⟨⟨⟨i₁, e₁⟩, ⟨i₂, e₂⟩⟩, rfl⟩ := (blockAddEquiv b f p q).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (indexAddEquiv a p q).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  simp only [Matrix.kronecker_apply, blockAddEquiv_apply, blockDilation_apply_eq_prod,
    Fin.prod_univ_add, indexEquiv_indexAddEquiv_left, indexEquiv_indexAddEquiv_right]

end QuantumChannelStein.TensorBlockReindex

noncomputable section
namespace QuantumChannelStein.TensorBlockReindex
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix TensorPower EnvironmentTensor

/-- Applying an environmental matrix leaves each output coordinate fixed. -/
theorem applyEnvironment_apply {a b e f : Type*} [Fintype b] [DecidableEq b] [Fintype f]
    (V : Matrix (b × f) a ℂ) (C : Matrix e f ℂ) (i : b) (j : e) (x : a) :
    applyEnvironment V C (i, j) x = ∑ l, C j l * V (i, l) x := by
  simp [applyEnvironment, Matrix.mul_apply, Matrix.one_apply,
    Fintype.sum_prod_type]

/-- Environmental application is compatible with separate bijections of
input, output, and both environment coordinate spaces. -/
theorem applyEnvironment_reindex {a b e f a' b' e' f' : Type*}
    [Fintype b] [DecidableEq b] [Fintype f]
    [Fintype b'] [DecidableEq b'] [Fintype f']
    (ea : a ≃ a') (eb : b ≃ b') (ee : e ≃ e') (ef : f ≃ f')
    (V : Matrix (b × f) a ℂ) (C : Matrix e f ℂ) :
    Matrix.reindex (Equiv.prodCongr eb ee) ea (applyEnvironment V C) =
      applyEnvironment (Matrix.reindex (Equiv.prodCongr eb ef) ea V)
        (Matrix.reindex ee ef C) := by
  ext ⟨i, j⟩ x
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_apply, applyEnvironment_apply]
  exact (ef.symm.sum_comp (fun l => C (ee.symm j) l * V (eb.symm i, l) (ea.symm x))).symm

/-- Environmental application commutes with a tensor product, with output
coordinates grouped separately from environmental coordinates. -/
theorem applyEnvironment_kronecker {a b e f a' b' e' f' : Type*}
    [Fintype b] [DecidableEq b] [Fintype f]
    [Fintype b'] [DecidableEq b'] [Fintype f']
    (V : Matrix (b × f) a ℂ) (W : Matrix (b' × f') a' ℂ)
    (C : Matrix e f ℂ) (D : Matrix e' f' ℂ) :
    Matrix.reindex (Equiv.prodProdProdComm b e b' e') (Equiv.refl (a × a'))
      (applyEnvironment V C ⊗ₖ applyEnvironment W D) =
      applyEnvironment
        (Matrix.reindex (Equiv.prodProdProdComm b f b' f') (Equiv.refl (a × a'))
          (V ⊗ₖ W)) (C ⊗ₖ D) := by
  ext ⟨⟨i, i'⟩, ⟨j, j'⟩⟩ ⟨x, x'⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodProdProdComm_symm,
    Equiv.prodProdProdComm_apply, Equiv.refl_symm, Equiv.refl_apply,
    Matrix.kronecker_apply, applyEnvironment_apply, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro l' _
  ring

variable {a b e f : Type*}
  [Fintype a] [Fintype b] [Fintype e] [Fintype f]
  [DecidableEq a] [DecidableEq b] [DecidableEq e] [DecidableEq f]

omit [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e] [DecidableEq f] in
/-- Flattening a block auxiliary matrix preserves the implemented physical
operator with the original tensor dilation. -/
theorem applyEnvironment_block_mul_reindex (V : Matrix (b × f) a ℂ) (k m : ℕ)
    (C : Matrix (Index (Index e k) m) (Index (Index f k) m) ℂ) :
    Matrix.reindex
      (Equiv.prodCongr (indexMulEquiv b k m) (indexMulEquiv e k m))
      (indexMulEquiv a k m)
      (applyEnvironment (blockDilation (blockDilation V k) m) C) =
        applyEnvironment (blockDilation V (k * m))
          (Matrix.reindex (indexMulEquiv e k m) (indexMulEquiv f k m) C) := by
  rw [applyEnvironment_reindex (indexMulEquiv a k m) (indexMulEquiv b k m)
    (indexMulEquiv e k m) (indexMulEquiv f k m), blockDilation_mul_reindex]

omit [DecidableEq e] [DecidableEq f] in
/-- The approximation error is unchanged on flattening block auxiliaries. -/
theorem block_mul_error (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ) (k m : ℕ)
    (C : Matrix (Index (Index e k) m) (Index (Index f k) m) ℂ) :
    ‖blockDilation U (k * m) - applyEnvironment (blockDilation V (k * m))
      (Matrix.reindex (indexMulEquiv e k m) (indexMulEquiv f k m) C)‖ =
      ‖blockDilation (blockDilation U k) m -
        applyEnvironment (blockDilation (blockDilation V k) m) C‖ := by
  rw [← applyEnvironment_block_mul_reindex, ← blockDilation_mul_reindex U k m]
  have heq :
      Matrix.reindex
        (Equiv.prodCongr (indexMulEquiv b k m) (indexMulEquiv e k m))
        (indexMulEquiv a k m) (blockDilation (blockDilation U k) m) -
      Matrix.reindex
        (Equiv.prodCongr (indexMulEquiv b k m) (indexMulEquiv e k m))
        (indexMulEquiv a k m) (applyEnvironment (blockDilation (blockDilation V k) m) C) =
      Matrix.reindex
        (Equiv.prodCongr (indexMulEquiv b k m) (indexMulEquiv e k m))
        (indexMulEquiv a k m)
        (blockDilation (blockDilation U k) m -
          applyEnvironment (blockDilation (blockDilation V k) m) C) := rfl
  rw [heq, norm_reindex]

omit [Fintype a] [Fintype e] [DecidableEq a] [DecidableEq e] [DecidableEq f] in
/-- The auxiliary tensor product implements the padded tensor operator. -/
theorem applyEnvironment_block_add_reindex (V : Matrix (b × f) a ℂ) (p q : ℕ)
    (C : Matrix (Index e p) (Index f p) ℂ)
    (D : Matrix (Index e q) (Index f q) ℂ) :
    Matrix.reindex (blockAddEquiv b e p q) (indexAddEquiv a p q)
      (applyEnvironment (blockDilation V p) C ⊗ₖ
        applyEnvironment (blockDilation V q) D) =
      applyEnvironment (blockDilation V (p + q))
        (Matrix.reindex (indexAddEquiv e p q) (indexAddEquiv f p q) (C ⊗ₖ D)) := by
  change Matrix.reindex
    (Equiv.prodCongr (indexAddEquiv b p q) (indexAddEquiv e p q)) (indexAddEquiv a p q)
    (Matrix.reindex
      (Equiv.prodProdProdComm (Index b p) (Index e p) (Index b q) (Index e q))
      (Equiv.refl _)
      (applyEnvironment (blockDilation V p) C ⊗ₖ
        applyEnvironment (blockDilation V q) D)) = _
  rw [applyEnvironment_kronecker, applyEnvironment_reindex (indexAddEquiv a p q)
    (indexAddEquiv b p q) (indexAddEquiv e p q) (indexAddEquiv f p q)]
  have h : Matrix.reindex
      (Equiv.prodCongr (indexAddEquiv b p q) (indexAddEquiv f p q)) (indexAddEquiv a p q)
      (Matrix.reindex
        (Equiv.prodProdProdComm (Index b p) (Index f p) (Index b q) (Index f q))
        (Equiv.refl _) (blockDilation V p ⊗ₖ blockDilation V q)) =
      blockDilation V (p + q) := blockDilation_add_reindex V p q
  rw [h]

/-- Pad an auxiliary matrix with a second exact-block auxiliary. -/
def padAuxiliary (p q : ℕ) (C : Matrix (Index e p) (Index f p) ℂ)
    (D : Matrix (Index e q) (Index f q) ℂ) :
    Matrix (Index e (p + q)) (Index f (p + q)) ℂ :=
  Matrix.reindex (indexAddEquiv e p q) (indexAddEquiv f p q) (C ⊗ₖ D)

/-- Padding costs at most the product of the two auxiliary norms. -/
theorem norm_padAuxiliary_le (p q : ℕ) (C : Matrix (Index e p) (Index f p) ℂ)
    (D : Matrix (Index e q) (Index f q) ℂ) :
    ‖padAuxiliary p q C D‖ ≤ ‖C‖ * ‖D‖ := by
  rw [padAuxiliary, norm_reindex]
  exact TensorAlgebra.kronecker_opNorm_le _ _

omit [DecidableEq f] in
/-- Exact contraction padding does not increase the physical approximation error. -/
theorem block_add_error_le (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ)
    (p q : ℕ) (C : Matrix (Index e p) (Index f p) ℂ)
    (D : Matrix (Index e q) (Index f q) ℂ)
    (hD : blockDilation U q = applyEnvironment (blockDilation V q) D)
    (hUq : ‖blockDilation U q‖ ≤ 1) :
    ‖blockDilation U (p + q) - applyEnvironment (blockDilation V (p + q))
      (padAuxiliary p q C D)‖ ≤
      ‖blockDilation U p - applyEnvironment (blockDilation V p) C‖ := by
  unfold padAuxiliary
  rw [← applyEnvironment_block_add_reindex, ← blockDilation_add_reindex U p q, ← hD]
  have heq :
      Matrix.reindex (blockAddEquiv b e p q) (indexAddEquiv a p q)
        (blockDilation U p ⊗ₖ blockDilation U q) -
      Matrix.reindex (blockAddEquiv b e p q) (indexAddEquiv a p q)
        (applyEnvironment (blockDilation V p) C ⊗ₖ blockDilation U q) =
      Matrix.reindex (blockAddEquiv b e p q) (indexAddEquiv a p q)
        (blockDilation U p ⊗ₖ blockDilation U q -
          applyEnvironment (blockDilation V p) C ⊗ₖ blockDilation U q) := rfl
  rw [heq, norm_reindex]
  exact TensorAlgebra.norm_kronecker_sub_le _ _ _ le_rfl hUq

/-- Flatten a fixed-block auxiliary onto the original environment tensor spaces. -/
def flattenAuxiliary (k m : ℕ)
    (C : Matrix (Index (Index e k) m) (Index (Index f k) m) ℂ) :
    Matrix (Index e (k * m)) (Index f (k * m)) ℂ :=
  Matrix.reindex (indexMulEquiv e k m) (indexMulEquiv f k m) C

omit [DecidableEq e] in
/-- The canonical flattening is isometric for auxiliary operator norms. -/
@[simp] theorem norm_flattenAuxiliary (k m : ℕ)
    (C : Matrix (Index (Index e k) m) (Index (Index f k) m) ℂ) :
    ‖flattenAuxiliary k m C‖ = ‖C‖ := norm_reindex _ _ _

omit [DecidableEq e] [DecidableEq f] in
/-- Fixed-block and original-space errors agree exactly after flattening. -/
theorem auxiliaryError_flattenAuxiliary
    (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ) (k m : ℕ)
    (C : Matrix (Index (Index e k) m) (Index (Index f k) m) ℂ) :
    UniformApproximation.auxiliaryError U V (k * m) (flattenAuxiliary k m C) =
      UniformApproximation.auxiliaryError (blockDilation U k) (blockDilation V k) m C :=
  block_mul_error U V k m C

omit [DecidableEq f] in
/-- Exact residual-block padding costs no additional approximation error. -/
theorem auxiliaryError_padAuxiliary_le
    (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ)
    (p q : ℕ) (C : Matrix (Index e p) (Index f p) ℂ)
    (D : Matrix (Index e q) (Index f q) ℂ)
    (hD : blockDilation U q = applyEnvironment (blockDilation V q) D)
    (hUq : ‖blockDilation U q‖ ≤ 1) :
    UniformApproximation.auxiliaryError U V (p + q) (padAuxiliary p q C D) ≤
      UniformApproximation.auxiliaryError U V p C :=
  block_add_error_le U V p q C D hD hUq

omit [DecidableEq f] in
/-- A global exact comparison supplies every residual padding block. -/
theorem auxiliaryError_pad_exact_le
    (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ)
    (D : Matrix e f ℂ) (hD : U = applyEnvironment V D) (hU : ‖U‖ ≤ 1)
    (p q : ℕ) (C : Matrix (Index e p) (Index f p) ℂ) :
    UniformApproximation.auxiliaryError U V (p + q)
      (padAuxiliary p q C (tensorPower D q)) ≤
      UniformApproximation.auxiliaryError U V p C := by
  apply auxiliaryError_padAuxiliary_le
  · rw [hD, UniformApproximation.blockDilation_environment]
  · exact UniformApproximation.norm_blockDilation_le_one U hU q

end QuantumChannelStein.TensorBlockReindex
