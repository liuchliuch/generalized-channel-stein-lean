import QuantumChannelStein.TensorExpansion

/-! # Actual environmental maps commute with tensor-word construction -/
noncomputable section
namespace QuantumChannelStein.EnvironmentTensor
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
open Matrix TensorPower TensorExpansion

/-- Coordinate formula for a mixed tensor word. -/
theorem wordTensor_apply_eq_prod {m n : Type*} (A H : Matrix m n ℂ) (k : ℕ)
    (w : Word k) (i : Index m k) (j : Index n k) :
    wordTensor A H k w i j = ∏ l : Fin k,
      (if indexEquiv Bool k w l then H else A) (indexEquiv m k i l) (indexEquiv n k j l) := by
  induction k with
  | zero => simp [wordTensor, tensorPower]
  | succ k ih =>
    change (if w.1 then H else A) i.1 j.1 * wordTensor A H k w.2 i.2 j.2 = _
    rw [Fin.prod_univ_succ, ih]
    simp only [indexEquiv_succ_zero, indexEquiv_succ_succ]

/-- Every factor of a tensor word may be composed with the same operator. -/
theorem wordTensor_mul_right {m n r : Type*} [Fintype n]
    (A H : Matrix m n ℂ) (V : Matrix n r ℂ) (k : ℕ) (w : Word k) :
    wordTensor (A * V) (H * V) k w = wordTensor A H k w * tensorPower V k := by
  induction k with
  | zero => ext i j; simp [wordTensor, tensorPower, Index, Matrix.mul_apply]
  | succ k ih =>
    rcases w with ⟨b,w⟩
    cases b <;> simp only [wordTensor, Bool.false_eq_true, ↓reduceIte,
      tensorPower_succ, ih, Matrix.mul_kronecker_mul]

/-- Fixed first factors can be regrouped away from a mixed tensor word. -/
theorem wordTensor_kronecker {m n r s : Type*}
    (B : Matrix m n ℂ) (A H : Matrix r s ℂ) (k : ℕ) (w : Word k) :
    Matrix.reindex (indexProdEquiv m r k) (indexProdEquiv n s k)
      (wordTensor (B ⊗ₖ A) (B ⊗ₖ H) k w) = tensorPower B k ⊗ₖ wordTensor A H k w := by
  ext ⟨i,j⟩ ⟨p,q⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, wordTensor_apply_eq_prod,
    indexEquiv_indexProdEquiv_symm, Matrix.kronecker_apply, tensorPower_apply_eq_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l _
  split <;> rfl

/-- Apply an auxiliary map to the fixed environment. -/
def applyEnvironment {a b e f : Type*} [Fintype b] [DecidableEq b] [Fintype f]
    (V : Matrix (b × f) a ℂ) (C : Matrix e f ℂ) : Matrix (b × e) a ℂ :=
  ((1 : Matrix b b ℂ) ⊗ₖ C) * V

/-- Tensor powers of a fixed dilation with outputs and environments canonically regrouped. -/
def blockDilation {a b f : Type*} (V : Matrix (b × f) a ℂ) (k : ℕ) :
    Matrix (Index b k × Index f k) (Index a k) ℂ :=
  Matrix.reindex (indexProdEquiv b f k) (Equiv.refl _) (tensorPower V k)

/-- The same auxiliary tensor word works for the whole fixed block dilation. -/
theorem environment_word {a b e f : Type*}
    [Fintype a] [Fintype b] [Fintype e] [Fintype f]
    [DecidableEq a] [DecidableEq b] [DecidableEq e] [DecidableEq f]
    (V : Matrix (b × f) a ℂ) (C H : Matrix e f ℂ) (k : ℕ) (w : Word k) :
    Matrix.reindex (indexProdEquiv b e k) (Equiv.refl _)
      (wordTensor (applyEnvironment V C) (applyEnvironment V H) k w) =
        ((1 : Matrix (Index b k) (Index b k) ℂ) ⊗ₖ wordTensor C H k w) * blockDilation V k := by
  unfold applyEnvironment
  rw [wordTensor_mul_right]
  have hreindex := Matrix.reindexLinearEquiv_mul ℂ ℂ
    (indexProdEquiv b e k) (indexProdEquiv b f k) (Equiv.refl (Index a k))
    (wordTensor ((1 : Matrix b b ℂ) ⊗ₖ C) ((1 : Matrix b b ℂ) ⊗ₖ H) k w) (tensorPower V k)
  simp only [Matrix.reindexLinearEquiv_apply] at hreindex
  rw [← hreindex, wordTensor_kronecker, tensorPower_one]
  rfl


/-- Environmental application is an actual complex-linear map. -/
def environmentLinear {a b e f : Type*} [Fintype b] [DecidableEq b] [Fintype f]
    (V : Matrix (b × f) a ℂ) : Matrix e f ℂ →ₗ[ℂ] Matrix (b × e) a ℂ where
  toFun := applyEnvironment V
  map_add' C H := by simp [applyEnvironment, Matrix.kronecker_add, Matrix.add_mul]
  map_smul' c C := by simp [applyEnvironment, Matrix.kronecker_smul, Matrix.smul_mul]

/-- The actual retained auxiliary sum implements the retained target-operator sum. -/
theorem environment_truncate {a b e f : Type*}
    [Fintype a] [Fintype b] [Fintype e] [Fintype f]
    [DecidableEq a] [DecidableEq b] [DecidableEq e] [DecidableEq f]
    (V : Matrix (b × f) a ℂ) (C H : Matrix e f ℂ) (k : ℕ) (u : ℝ) :
    Matrix.reindex (indexProdEquiv b e k) (Equiv.refl _)
      (truncateAt (applyEnvironment V C) (applyEnvironment V H) k u) =
        applyEnvironment (blockDilation V k) (truncateAt C H k u) := by
  have hsum : Matrix.reindex (indexProdEquiv b e k) (Equiv.refl (Index a k))
      (truncateAt (applyEnvironment V C) (applyEnvironment V H) k u) =
      ∑ w ∈ (Finset.univ : Finset (Word k)).filter (fun w => (weight k w : ℝ) ≤ u),
        Matrix.reindex (indexProdEquiv b e k) (Equiv.refl (Index a k))
          (wordTensor (applyEnvironment V C) (applyEnvironment V H) k w) := by
    ext i j
    simp [truncateAt, Matrix.reindex_apply, Matrix.sum_apply]
  rw [hsum]
  simp_rw [environment_word]
  change (∑ w ∈ (Finset.univ : Finset (Word k)).filter (fun w => (weight k w : ℝ) ≤ u),
      environmentLinear (blockDilation V k) (wordTensor C H k w)) =
    environmentLinear (blockDilation V k) (truncateAt C H k u)
  simp [truncateAt, map_sum]

/-- The block error is exactly the norm of its unreindexed tensor truncation. -/
theorem environment_truncate_error {a b e f : Type*}
    [Fintype a] [Fintype b] [Fintype e] [Fintype f]
    [DecidableEq a] [DecidableEq b] [DecidableEq e] [DecidableEq f]
    (V : Matrix (b × f) a ℂ) (C H : Matrix e f ℂ) (k : ℕ) (u : ℝ) :
    ‖blockDilation (applyEnvironment V C + applyEnvironment V H) k -
      applyEnvironment (blockDilation V k) (truncateAt C H k u)‖ =
    ‖tensorPower (applyEnvironment V C + applyEnvironment V H) k -
      truncateAt (applyEnvironment V C) (applyEnvironment V H) k u‖ := by
  rw [← environment_truncate]
  unfold blockDilation
  have hsub : Matrix.reindex (indexProdEquiv b e k) (Equiv.refl (Index a k))
      (tensorPower (applyEnvironment V C + applyEnvironment V H) k) -
      Matrix.reindex (indexProdEquiv b e k) (Equiv.refl (Index a k))
        (truncateAt (applyEnvironment V C) (applyEnvironment V H) k u) =
      Matrix.reindex (indexProdEquiv b e k) (Equiv.refl (Index a k))
        (tensorPower (applyEnvironment V C + applyEnvironment V H) k -
          truncateAt (applyEnvironment V C) (applyEnvironment V H) k u) := rfl
  rw [hsub, TensorPower.norm_reindex]

end QuantumChannelStein.EnvironmentTensor

