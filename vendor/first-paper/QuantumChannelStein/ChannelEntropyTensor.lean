import QuantumChannelStein.RelativeEntropyReindex

/-! # Product pure inputs and channel-divergence tensor superadditivity -/

noncomputable section
namespace QuantumChannelStein.ChannelEntropy

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

variable {n m a b r s : ℕ}

/-- Product pure input with the two reference coordinates grouped first. -/
def productInputVector (ψ : EuclideanSpace ℂ (Fin n × Fin n))
    (φ : EuclideanSpace ℂ (Fin a × Fin a)) :
    EuclideanSpace ℂ (Fin (n * a) × Fin (n * a)) :=
  WithLp.toLp 2 (fun p =>
    ψ ((MatrixMap.choiShuffle n n a a).symm p).1 *
      φ ((MatrixMap.choiShuffle n n a a).symm p).2)

theorem productInputVector_norm_sq (ψ : EuclideanSpace ℂ (Fin n × Fin n))
    (φ : EuclideanSpace ℂ (Fin a × Fin a)) :
    ‖productInputVector ψ φ‖ ^ 2 = ‖ψ‖ ^ 2 * ‖φ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ p, ‖ψ ((MatrixMap.choiShuffle n n a a).symm p).1 *
    φ ((MatrixMap.choiShuffle n n a a).symm p).2‖ ^ 2) = _
  calc
    _ = ∑ p : (Fin n × Fin n) × (Fin a × Fin a), ‖ψ p.1 * φ p.2‖ ^ 2 :=
      Equiv.sum_comp (MatrixMap.choiShuffle n n a a).symm (fun p => ‖ψ p.1 * φ p.2‖ ^ 2)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [norm_mul, mul_pow, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      simp only [EuclideanSpace.norm_sq_eq]

/-- A normalized product of two normalized reference-assisted pure inputs. -/
def productInput (ψ : UnitPureInput n n) (φ : UnitPureInput a a) : UnitPureInput (n * a) (n * a) :=
  ⟨productInputVector ψ.val φ.val, by
    have h := productInputVector_norm_sq ψ.val φ.val
    rw [ψ.property, φ.property] at h
    nlinarith [norm_nonneg (productInputVector ψ.val φ.val)]⟩

theorem pureMatrix_productInput (ψ : UnitPureInput n n) (φ : UnitPureInput a a) :
    pureMatrix (productInput ψ φ).val =
      Matrix.reindex (MatrixMap.choiShuffle n n a a) (MatrixMap.choiShuffle n n a a)
        (pureMatrix ψ.val ⊗ₖ pureMatrix φ.val) := by
  ext p q
  simp only [productInput, productInputVector, pureMatrix, WithLp.ofLp_toLp,
    Matrix.vecMulVec_apply, Pi.star_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, StarMul.star_mul]
  ring

/-- The actual amplified tensor channel sends regrouped product inputs
to the corresponding regrouped product outputs. -/
theorem amplify_tensor_product (Φ : KrausChannel n m) (Γ : KrausChannel a b)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (Y : Matrix (Fin s × Fin a) (Fin s × Fin a) ℂ) :
    (Φ.tensor Γ).amplify (r * s)
      (Matrix.reindex (MatrixMap.choiShuffle r n s a) (MatrixMap.choiShuffle r n s a) (X ⊗ₖ Y)) =
      Matrix.reindex (MatrixMap.choiShuffle r m s b) (MatrixMap.choiShuffle r m s b)
        (Φ.amplify r X ⊗ₖ Γ.amplify s Y) := by
  ext ⟨i, u⟩ ⟨j, v⟩
  rw [KrausChannel.amplify_block]
  have hblock :
      (fun x y => Matrix.reindex (MatrixMap.choiShuffle r n s a) (MatrixMap.choiShuffle r n s a)
        (X ⊗ₖ Y) (i, x) (j, y)) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((fun x y => X ((finProdFinEquiv.symm i).1, x) ((finProdFinEquiv.symm j).1, y)) ⊗ₖ
          (fun x y => Y ((finProdFinEquiv.symm i).2, x) ((finProdFinEquiv.symm j).2, y))) := by
    ext x y
    rfl
  rw [hblock, KrausChannel.tensor_apply_product]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, MatrixMap.choiShuffle,
    Equiv.coe_fn_symm_mk, Matrix.kroneckerMap_apply, KrausChannel.amplify_block]

/-- Permutation from the tensor of two flattened output states to the
flattened reference-grouped output of the tensor channel. -/
def outputRegroup (n m a b : ℕ) : Fin ((n * m) * (a * b)) ≃ Fin ((n * a) * (m * b)) :=
  finProdFinEquiv.symm.trans
    ((finProdFinEquiv.symm.prodCongr finProdFinEquiv.symm).trans
      ((MatrixMap.choiShuffle n m a b).trans finProdFinEquiv))

/-- Equality of the actual output states after their explicit permutation. -/
theorem pureOutput_productInput (Φ : KrausChannel n m) (Γ : KrausChannel a b)
    (ψ : UnitPureInput n n) (φ : UnitPureInput a a) :
    pureOutput (Φ.tensor Γ) (productInput ψ φ) =
      ((pureOutput Φ ψ).tensor (pureOutput Γ φ)).reindex (outputRegroup n m a b) := by
  apply state_eq_of_matrix_eq
  rw [pureOutput_matrix, pureMatrix_productInput, amplify_tensor_product]
  ext i j
  simp [State.reindex_matrix, State.tensor_matrix, pureOutput_matrix, outputRegroup,
    Matrix.reindex_apply]

/-- Product inputs attain the sum of their individual output divergences. -/
theorem umegaki_productInput (Φ Ψ : KrausChannel n m) (Γ Θ : KrausChannel a b)
    (ψ : UnitPureInput n n) (φ : UnitPureInput a a) :
    RelativeEntropy.umegaki (pureOutput (Φ.tensor Γ) (productInput ψ φ))
      (pureOutput (Ψ.tensor Θ) (productInput ψ φ)) =
      RelativeEntropy.umegaki (pureOutput Φ ψ) (pureOutput Ψ ψ) +
        RelativeEntropy.umegaki (pureOutput Γ φ) (pureOutput Θ φ) := by
  rw [pureOutput_productInput, pureOutput_productInput,
    RelativeEntropy.umegaki_reindex, RelativeEntropy.umegaki_tensor]

/-- Channel Umegaki divergence is superadditive for actual independent
tensor products. No optimizer is assumed to exist. -/
theorem channelD_tensor_superadditive (Φ Ψ : KrausChannel n m) (Γ Θ : KrausChannel a b) :
    channelD Φ Ψ + channelD Γ Θ ≤ channelD (Φ.tensor Γ) (Ψ.tensor Θ) := by
  apply EReal.add_le_of_forall_lt
  intro x hx y hy
  obtain ⟨ψ, hψ⟩ := lt_iSup_iff.mp hx
  obtain ⟨φ, hφ⟩ := lt_iSup_iff.mp hy
  calc
    x + y ≤ RelativeEntropy.umegaki (pureOutput Φ ψ) (pureOutput Ψ ψ) +
        RelativeEntropy.umegaki (pureOutput Γ φ) (pureOutput Θ φ) := add_le_add hψ.le hφ.le
    _ = RelativeEntropy.umegaki (pureOutput (Φ.tensor Γ) (productInput ψ φ))
        (pureOutput (Ψ.tensor Θ) (productInput ψ φ)) := (umegaki_productInput Φ Ψ Γ Θ ψ φ).symm
    _ ≤ channelD (Φ.tensor Γ) (Ψ.tensor Θ) :=
      umegaki_pureOutput_le_channelD _ _ _

end QuantumChannelStein.ChannelEntropy
