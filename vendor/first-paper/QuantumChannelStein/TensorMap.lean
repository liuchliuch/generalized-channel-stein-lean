import QuantumChannelStein.TensorChannel
import QuantumChannelStein.CPOrder

/-! # Tensor product of arbitrary complex-linear matrix maps -/
noncomputable section
namespace QuantumChannelStein.MatrixMap
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
variable {n m a b : ℕ}

/-- Tensor product by linear extension of products of matrix units. -/
def tensor (Φ : MatrixMap n m) (Ψ : MatrixMap a b) : MatrixMap (n * a) (m * b) where
  toFun X := ∑ i : Fin n × Fin a, ∑ j : Fin n × Fin a,
    X (finProdFinEquiv i) (finProdFinEquiv j) •
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Φ (Matrix.single i.1 j.1 1) ⊗ₖ Ψ (Matrix.single i.2 j.2 1))
  map_add' X Y := by simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Matrix.smul_apply, Finset.smul_sum, smul_smul]

/-- The tensor product has the expected action on paired matrix units. -/
theorem tensor_single (Φ : MatrixMap n m) (Ψ : MatrixMap a b)
    (i j : Fin n × Fin a) :
    tensor Φ Ψ (Matrix.single (finProdFinEquiv i) (finProdFinEquiv j) 1) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Φ (Matrix.single i.1 j.1 1) ⊗ₖ Ψ (Matrix.single i.2 j.2 1)) := by
  simp [tensor, Matrix.single, finProdFinEquiv.injective.eq_iff, ite_and]

/-- Tensoring is additive in the first channel argument. -/
theorem tensor_add_left (Φ Ω : MatrixMap n m) (Ψ : MatrixMap a b) :
    tensor (Φ + Ω) Ψ = tensor Φ Ψ + tensor Ω Ψ := by
  ext X i j
  simp [tensor, Matrix.add_kronecker, Matrix.sum_apply, Finset.sum_add_distrib,
    Matrix.smul_apply, mul_add]

/-- Tensoring is additive in the second channel argument. -/
theorem tensor_add_right (Φ : MatrixMap n m) (Ψ Ω : MatrixMap a b) :
    tensor Φ (Ψ + Ω) = tensor Φ Ψ + tensor Φ Ω := by
  ext X i j
  simp [tensor, Matrix.kronecker_add, Matrix.sum_apply, Finset.sum_add_distrib,
    Matrix.smul_apply, mul_add]


/-- Canonical reshuffling from two Choi index pairs to the product-channel pair. -/
def choiShuffle (n m a b : ℕ) :
    ((Fin n × Fin m) × (Fin a × Fin b)) ≃ (Fin (n * a) × Fin (m * b)) where
  toFun x := (finProdFinEquiv (x.1.1, x.2.1), finProdFinEquiv (x.1.2, x.2.2))
  invFun x := (((finProdFinEquiv.symm x.1).1, (finProdFinEquiv.symm x.2).1),
    ((finProdFinEquiv.symm x.1).2, (finProdFinEquiv.symm x.2).2))
  left_inv := by rintro ⟨⟨i,j⟩,⟨k,l⟩⟩; simp
  right_inv := by
    rintro ⟨i,j⟩
    change (finProdFinEquiv (finProdFinEquiv.symm i), finProdFinEquiv (finProdFinEquiv.symm j)) = (i,j)
    simp only [Equiv.apply_symm_apply]

@[simp] theorem choiShuffle_symm_apply (i : Fin n) (j : Fin m) (k : Fin a) (l : Fin b) :
    (choiShuffle n m a b).symm (finProdFinEquiv (i,k), finProdFinEquiv (j,l)) = ((i,j),(k,l)) := by
  change (((finProdFinEquiv.symm (finProdFinEquiv (i,k))).1,
    (finProdFinEquiv.symm (finProdFinEquiv (j,l))).1),
    ((finProdFinEquiv.symm (finProdFinEquiv (i,k))).2,
    (finProdFinEquiv.symm (finProdFinEquiv (j,l))).2)) = _
  simp only [Equiv.symm_apply_apply]

/-- The tensor-product Choi operator is the actual Kronecker product with a
canonical rearrangement of reference/output coordinates. -/
theorem choi_tensor (Φ : MatrixMap n m) (Ψ : MatrixMap a b) :
    choi (tensor Φ Ψ) = Matrix.reindex (choiShuffle n m a b) (choiShuffle n m a b)
      (choi Φ ⊗ₖ choi Ψ) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i,k⟩,rfl⟩ := (finProdFinEquiv (m := n) (n := a)).surjective i
  obtain ⟨⟨j,l⟩,rfl⟩ := (finProdFinEquiv (m := n) (n := a)).surjective j
  obtain ⟨⟨u,w⟩,rfl⟩ := (finProdFinEquiv (m := m) (n := b)).surjective u
  obtain ⟨⟨v,x⟩,rfl⟩ := (finProdFinEquiv (m := m) (n := b)).surjective v
  simp only [choi, tensor_single, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, choiShuffle_symm_apply, Matrix.kronecker_apply]

/-- Kronecker products of PSD matrices are PSD, proved by explicit Gram factors. -/
theorem posSemidef_kronecker {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊗ₖ B).PosSemidef := by
  obtain ⟨C,hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨D,hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  change A = Cᴴ * C at hC
  change B = Dᴴ * D at hD
  rw [hC, hD, Matrix.mul_kronecker_mul, ← Matrix.conjTranspose_kronecker]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Complete positivity is closed under the actual tensor product of linear maps. -/
theorem completelyPositive_tensor {Φ : MatrixMap n m} {Ψ : MatrixMap a b}
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ) :
    CompletelyPositive (tensor Φ Ψ) := by
  rw [completelyPositive_iff_choi_positive, choi_tensor]
  exact (posSemidef_kronecker ((completelyPositive_iff_choi_positive Φ).mp hΦ)
    ((completelyPositive_iff_choi_positive Ψ).mp hΨ)).submatrix _


@[simp] theorem tensor_sub_left (Φ Ω : MatrixMap n m) (Ψ : MatrixMap a b) :
    tensor (Φ - Ω) Ψ = tensor Φ Ψ - tensor Ω Ψ := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [sub_add_cancel] using (tensor_add_left (Φ - Ω) Ω Ψ).symm

@[simp] theorem tensor_sub_right (Φ : MatrixMap n m) (Ψ Ω : MatrixMap a b) :
    tensor Φ (Ψ - Ω) = tensor Φ Ψ - tensor Φ Ω := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [sub_add_cancel] using (tensor_add_right Φ (Ψ - Ω) Ω).symm

@[simp] theorem tensor_smul_left (c : ℂ) (Φ : MatrixMap n m) (Ψ : MatrixMap a b) :
    tensor (c • Φ) Ψ = c • tensor Φ Ψ := by
  ext X i j
  simp [tensor, Matrix.smul_kronecker, Matrix.sum_apply, Matrix.smul_apply,
    Finset.mul_sum, mul_left_comm]

@[simp] theorem tensor_smul_right (c : ℂ) (Φ : MatrixMap n m) (Ψ : MatrixMap a b) :
    tensor Φ (c • Ψ) = c • tensor Φ Ψ := by
  ext X i j
  simp [tensor, Matrix.kronecker_smul, Matrix.sum_apply, Matrix.smul_apply,
    Finset.mul_sum, mul_left_comm]

theorem completelyPositive_add {Φ Ψ : MatrixMap n m}
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ) : CompletelyPositive (Φ + Ψ) := by
  rw [completelyPositive_iff_choi_positive, choi_add]
  exact ((completelyPositive_iff_choi_positive Φ).mp hΦ).add
    ((completelyPositive_iff_choi_positive Ψ).mp hΨ)

theorem completelyPositive_smul {Φ : MatrixMap n m} {c : ℝ}
    (hc : 0 ≤ c) (hΦ : CompletelyPositive Φ) : CompletelyPositive ((c : ℂ) • Φ) := by
  rw [completelyPositive_iff_choi_positive, choi_smul]
  exact ((completelyPositive_iff_choi_positive Φ).mp hΦ).smul (by exact_mod_cast hc)

/-- CP domination is preserved by tensoring two CP comparisons. -/
theorem cpLe_tensor {Φ Ω : MatrixMap n m} {Ψ Θ : MatrixMap a b}
    (hΦ : CompletelyPositive Φ) (hΘ : CompletelyPositive Θ)
    (h₁ : CPLe Φ Ω) (h₂ : CPLe Ψ Θ) : CPLe (tensor Φ Ψ) (tensor Ω Θ) := by
  change CompletelyPositive (tensor Ω Θ - tensor Φ Ψ)
  have hdecomp : tensor Ω Θ - tensor Φ Ψ =
      tensor (Ω - Φ) Θ + tensor Φ (Θ - Ψ) := by
    rw [tensor_sub_left, tensor_sub_right]
    abel
  rw [hdecomp]
  exact completelyPositive_add (completelyPositive_tensor h₁ hΘ)
    (completelyPositive_tensor hΦ h₂)

/-- Exact product matrix-unit identity for canonical flattened coordinates. -/
theorem reindex_product_single (i j : Fin n) (k l : Fin a) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.single i j (1 : ℂ) ⊗ₖ Matrix.single k l 1) =
        Matrix.single (finProdFinEquiv (i,k)) (finProdFinEquiv (j,l)) 1 := by
  rw [Matrix.single_kronecker_single, one_mul]
  ext u v
  change (if (i,k) = finProdFinEquiv.symm u ∧ (j,l) = finProdFinEquiv.symm v then (1 : ℂ) else 0) =
    (if finProdFinEquiv (i,k) = u ∧ finProdFinEquiv (j,l) = v then 1 else 0)
  simp only [Equiv.eq_symm_apply]

/-- The abstract linear tensor product agrees with the explicitly paired
normalized Kraus construction on all input matrices. -/
theorem tensor_kraus_toLinearMap (Φ : KrausChannel n m) (Ψ : KrausChannel a b) :
    tensor Φ.toLinearMap Ψ.toLinearMap = (KrausChannel.tensor Φ Ψ).toLinearMap := by
  apply choi_injective
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i,k⟩,rfl⟩ := (finProdFinEquiv (m := n) (n := a)).surjective i
  obtain ⟨⟨j,l⟩,rfl⟩ := (finProdFinEquiv (m := n) (n := a)).surjective j
  have h := KrausChannel.tensor_apply_product Φ Ψ (Matrix.single i j 1) (Matrix.single k l 1)
  rw [reindex_product_single] at h
  change (tensor Φ.toLinearMap Ψ.toLinearMap (Matrix.single _ _ 1)) u v = _
  rw [tensor_single]
  exact congrFun (congrFun h.symm u) v

end QuantumChannelStein.MatrixMap


