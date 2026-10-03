import GeneralizedChannelStein.ChannelTransport
import QuantumChannelStein.ChannelDilationPower

/-! # Tensoring arbitrary prescribed dilations without changing channel semantics -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.DilationTensor
open QuantumChannelStein Matrix ChannelPowerReindex ChannelDilationPower
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
variable {a b c d e f : ℕ}

def outputEquiv (b e d f : ℕ) : (Fin b × Fin e) × (Fin d × Fin f) ≃
    Fin (b*d) × Fin (e*f) :=
  (Equiv.prodProdProdComm _ _ _ _).trans (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)

def tensorDilation (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin d × Fin f) (Fin c) ℂ) :
    Matrix (Fin (b*d) × Fin (e*f)) (Fin (a*c)) ℂ :=
  Matrix.reindex (outputEquiv b e d f) finProdFinEquiv (V ⊗ₖ W)

@[simp] theorem tensorDilation_apply (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin d × Fin f) (Fin c) ℂ)
    (i : Fin b) (j : Fin d) (u : Fin e) (v : Fin f) (x : Fin a) (y : Fin c) :
    tensorDilation V W (finProdFinEquiv (i,j),finProdFinEquiv (u,v)) (finProdFinEquiv (x,y)) =
      V (i,u) x * W (j,v) y := by
  simp [tensorDilation, outputEquiv, Matrix.reindex_apply, Matrix.kroneckerMap_apply]

theorem tensorDilation_norm (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin d × Fin f) (Fin c) ℂ) :
    ‖tensorDilation V W‖ ≤ ‖V‖ * ‖W‖ := by
  rw [tensorDilation, TensorPower.norm_reindex]
  exact TensorAlgebra.kronecker_opNorm_le _ _

theorem tensorDilation_sub_left (V U : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin d × Fin f) (Fin c) ℂ) :
    tensorDilation (V-U) W = tensorDilation V W - tensorDilation U W := by
  ext i j
  simp [tensorDilation, Matrix.reindex_apply, Matrix.kroneckerMap_apply, sub_mul]

theorem tensorDilation_isometry (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin d × Fin f) (Fin c) ℂ)
    (hV : Vᴴ*V=1) (hW : Wᴴ*W=1) :
    (tensorDilation V W)ᴴ * tensorDilation V W = 1 := by
  apply reindex_isometry
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hV,hW,Matrix.one_kronecker_one]

/-- Arbitrary, including unnormalized, dilation tensors realize the actual
matrix-map tensor product. -/
theorem dilationMap_tensorDilation (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin d × Fin f) (Fin c) ℂ) :
    dilationMap (tensorDilation V W) = MatrixMap.tensor (dilationMap V) (dilationMap W) := by
  apply MatrixMap.choi_injective
  ext ⟨x,i⟩ ⟨y,j⟩
  obtain ⟨⟨x1,x2⟩,rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨y1,y2⟩,rfl⟩ := finProdFinEquiv.surjective y
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  change (dilationMap (tensorDilation V W)) (Matrix.single (finProdFinEquiv (x1,x2))
    (finProdFinEquiv (y1,y2)) 1) (finProdFinEquiv (i1,i2)) (finProdFinEquiv (j1,j2)) =
    MatrixMap.tensor (dilationMap V) (dilationMap W) (Matrix.single (finProdFinEquiv (x1,x2))
    (finProdFinEquiv (y1,y2)) 1) (finProdFinEquiv (i1,i2)) (finProdFinEquiv (j1,j2))
  rw [MatrixMap.tensor_single]
  simp only [choi_dilationMap, dilationColumns, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.reindex_apply, Matrix.kroneckerMap_apply]
  simp [dilationMap, MatrixMap.ofKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single, tensorDilation_apply, ← finProdFinEquiv.sum_comp,
    Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc,
    ite_and]
  exact Finset.sum_comm

/-- Input/output coordinate transport of a dilation preserves its represented map. -/
theorem dilationMap_reindex {a' b' : ℕ}
    (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) :
    dilationMap (Matrix.reindex (Equiv.prodCongr eb (Equiv.refl (Fin e))) ea V) =
      ChannelTransport.reindexMap ea eb (dilationMap V) := by
  apply MatrixMap.choi_injective
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [MatrixMap.choi, ChannelTransport.reindexMap_apply, dilationMap, MatrixMap.ofKraus,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply,
    Matrix.single, ← ea.symm_apply_eq, ite_and]

/-- Auxiliary tensor product in the concrete finite environment coordinates. -/
def tensorAuxiliary {g h : ℕ} (A : Matrix (Fin e) (Fin f) ℂ)
    (B : Matrix (Fin g) (Fin h) ℂ) : Matrix (Fin (e*g)) (Fin (f*h)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B)

theorem tensorAuxiliary_norm {g h : ℕ} (A : Matrix (Fin e) (Fin f) ℂ)
    (B : Matrix (Fin g) (Fin h) ℂ) : ‖tensorAuxiliary A B‖ ≤ ‖A‖ * ‖B‖ := by
  rw [tensorAuxiliary, TensorPower.norm_reindex]
  exact TensorAlgebra.kronecker_opNorm_le _ _

theorem tensorDilation_environment {g h : ℕ}
    (V : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (W : Matrix (Fin d × Fin h) (Fin c) ℂ)
    (A : Matrix (Fin e) (Fin f) ℂ) (B : Matrix (Fin g) (Fin h) ℂ) :
    tensorDilation (EnvironmentTensor.applyEnvironment V A) (EnvironmentTensor.applyEnvironment W B) =
      EnvironmentTensor.applyEnvironment (tensorDilation V W) (tensorAuxiliary A B) := by
  ext ⟨i,j⟩ x
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨x1,x2⟩,rfl⟩ := finProdFinEquiv.surjective x
  have hd (x : Fin f) (y : Fin h) : (finProdFinEquiv (x,y)).divNat = x :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (x,y))
  have hm (x : Fin f) (y : Fin h) : (finProdFinEquiv (x,y)).modNat = y :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (x,y))
  simp [tensorDilation_apply, TensorBlockReindex.applyEnvironment_apply,
    tensorAuxiliary, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    mul_comm,mul_left_comm,mul_assoc,hd,hm]
  exact Finset.sum_comm

end GeneralizedChannelStein.DilationTensor
