import GeneralizedChannelStein.QuantitativeFamilies
import QuantumChannelStein.UniformApproximation
import QuantumChannelStein.TestingSDP

/-! # Actual weighted discarding is unital CP and operator-norm contractive -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelEntropy
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b d : ℕ}

/-- Genuine Heisenberg adjoint of a finite Kraus channel. -/
def heisenbergMap (Φ : KrausChannel a b) : MatrixMap b a :=
  MatrixMap.ofKraus (fun i => (Φ.kraus i)ᴴ)

theorem heisenbergMap_cp (Φ : KrausChannel a b) : MatrixMap.CompletelyPositive (heisenbergMap Φ) :=
  MatrixMap.completelyPositive_ofKraus _

theorem heisenbergMap_apply (Φ : KrausChannel a b) (X : Operator b) :
    heisenbergMap Φ X = ∑ i, (Φ.kraus i)ᴴ*X*Φ.kraus i := by
  simp [heisenbergMap,MatrixMap.ofKraus]

theorem heisenbergMap_one (Φ : KrausChannel a b) : heisenbergMap Φ 1 = 1 := by
  rw [heisenbergMap_apply]
  simpa using Φ.normalized

/-- The map really is the adjoint for the Hilbert--Schmidt trace pairing. -/
theorem heisenbergMap_pairing (Φ : KrausChannel a b) (X : Operator b) (Y : Operator a) :
    (Y*heisenbergMap Φ X).trace = (Φ.apply Y*X).trace := by
  rw [heisenbergMap_apply]
  simp only [KrausChannel.apply,Matrix.mul_sum,Matrix.sum_mul,Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Y*((Φ.kraus i)ᴴ*X*Φ.kraus i) = (Y*(Φ.kraus i)ᴴ*X)*Φ.kraus i by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  congr 1
  simp only [Matrix.mul_assoc]

/-- Stinespring compression, used for the full operator norm (not only Hermitian inputs). -/
theorem heisenbergMap_dilation (Φ : KrausChannel a b) (X : Operator b) :
    heisenbergMap Φ X = Φ.stinespringᴴ*(X ⊗ₖ (1:Operator Φ.rank))*Φ.stinespring := by
  rw [heisenbergMap_apply]
  ext i j
  simp only [KrausChannel.stinespring,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.sum_apply,Fintype.sum_prod_type,Matrix.kroneckerMap_apply,Matrix.one_apply]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_one]

theorem norm_heisenbergMap_le (Φ : KrausChannel a b) (X : Operator b) :
    ‖heisenbergMap Φ X‖ ≤ ‖X‖ := by
  rw [heisenbergMap_dilation]
  have hV : ‖Φ.stinespring‖ ≤ 1 := UniformApproximation.norm_isometry_le_one _ Φ.stinespring_isometry
  calc
    _ ≤ ‖Φ.stinespringᴴ‖*‖X ⊗ₖ (1:Operator Φ.rank)‖*‖Φ.stinespring‖ :=
      (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1*‖X‖*1 := by
      gcongr
      · simpa only [Matrix.l2_opNorm_conjTranspose] using hV
      · exact TensorNorm.kronecker_one_opNorm_le X
    _ = _ := by ring

/-- Weighted discarding on flattened coordinates is the actual adjoint of preparation. -/
def weightedDiscardMap (a : ℕ) (τ : State b) : MatrixMap (a*b) a := heisenbergMap (appendState a τ)

theorem weightedDiscardMap_cp (a : ℕ) (τ : State b) :
    MatrixMap.CompletelyPositive (weightedDiscardMap a τ) := heisenbergMap_cp _

theorem weightedDiscardMap_one (a : ℕ) (τ : State b) : weightedDiscardMap a τ 1 = 1 :=
  heisenbergMap_one _

theorem norm_weightedDiscardMap_le (a : ℕ) (τ : State b) (X : Operator (a*b)) :
    ‖weightedDiscardMap a τ X‖ ≤ ‖X‖ := norm_heisenbergMap_le _ _

/-- The physical weighted partial-trace formula, with the positive square root on both sides. -/
def weightedDiscard (τ : State b) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : Operator a :=
  KrausChannel.traceOutput (((1:Operator a) ⊗ₖ CFC.sqrt τ.matrix)*X*((1:Operator a) ⊗ₖ CFC.sqrt τ.matrix))

theorem weightedDiscard_pairing (τ : State b) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (Y : Operator a) : (Y*weightedDiscard τ X).trace = ((Y ⊗ₖ τ.matrix)*X).trace := by
  let R := (1:Operator a) ⊗ₖ CFC.sqrt τ.matrix
  change (Y*KrausChannel.traceEnvironment (R*X*R)).trace = _
  rw [trace_partialTrace_duality]
  change ((Y ⊗ₖ (1:Operator b))*(R*X*R)).trace = _
  rw [show (Y ⊗ₖ (1:Operator b))*(R*X*R) = ((Y ⊗ₖ (1:Operator b))*R*X)*R by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  have hR : R*(Y ⊗ₖ (1:Operator b))*R = Y ⊗ₖ τ.matrix := by
    dsimp [R]
    rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul,Matrix.mul_one,CFC.sqrt_mul_sqrt_self τ.matrix τ.positive.nonneg]
  simpa only [← Matrix.mul_assoc,hR]

/-- No abstract conditional expectation is assumed: the sandwich is the adjoint of actual preparation. -/
theorem weightedDiscard_eq_map (τ : State b) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    weightedDiscard τ X = weightedDiscardMap a τ (Matrix.reindex finProdFinEquiv finProdFinEquiv X) := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro Y
  rw [weightedDiscard_pairing,weightedDiscardMap,heisenbergMap_pairing,appendState_apply]
  change _ = (((Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv) (Y ⊗ₖ τ.matrix)) *
    ((Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv) X)).trace
  rw [Matrix.reindexLinearEquiv_mul]
  exact (ChannelEntropy.trace_reindex_equiv _ _).symm

/-- The physical sandwich conditional expectation is contractive on every operator. -/
theorem norm_weightedDiscard_le (τ : State b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : ‖weightedDiscard τ X‖ ≤ ‖X‖ := by
  rw [weightedDiscard_eq_map]
  exact (norm_weightedDiscardMap_le a τ _).trans_eq (TensorPower.norm_reindex _ _ _)

theorem weightedDiscard_one (τ : State b) :
    weightedDiscard τ (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) = 1 := by
  rw [weightedDiscard_eq_map]
  have h : Matrix.reindex finProdFinEquiv finProdFinEquiv
      (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) = 1 := by
    exact Matrix.reindexLinearEquiv_one ℂ ℂ finProdFinEquiv
  rw [h,weightedDiscardMap_one]

/-- Exact damping on a product operator, the key weighted-discarding identity. -/
theorem weightedDiscard_tensor (τ : State b) (A : Operator a) (B : Operator b) :
    weightedDiscard τ (A ⊗ₖ B) = (τ.matrix*B).trace • A := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro Y
  rw [weightedDiscard_pairing, ← Matrix.mul_kronecker_mul,Matrix.trace_kronecker,
    Matrix.mul_smul,Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

theorem weightedDiscard_add (τ : State b)
    (X Y : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    weightedDiscard τ (X+Y) = weightedDiscard τ X+weightedDiscard τ Y := by
  simp only [weightedDiscard,Matrix.mul_add,Matrix.add_mul]
  ext i j
  simp [KrausChannel.traceOutput,Finset.sum_add_distrib]

theorem weightedDiscard_smul (τ : State b) (c : ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    weightedDiscard τ (c • X) = c • weightedDiscard τ X := by
  simp only [weightedDiscard,Matrix.mul_smul,Matrix.smul_mul]
  ext i j
  simp [KrausChannel.traceOutput,Finset.mul_sum]

end GeneralizedChannelStein
