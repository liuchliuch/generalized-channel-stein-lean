import QuantumChannelStein.ChannelComposition

/-! # Actual sequential realization of a tensor product on an entangled input -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SequentialTensor
open Matrix ChannelEntropy OperationalTesting
open scoped BigOperators Kronecker
variable {r a b c d : ℕ}

def tripleLeft (r a c : ℕ) : Fin ((r * a) * c) ≃ (Fin r × Fin a) × Fin c :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))

def tripleRight (r a c : ℕ) : Fin (r * (a * c)) ≃ Fin r × (Fin a × Fin c) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

/-- Move the first channel input to the exposed final register. -/
def expose (r a c : ℕ) : Fin (r * (a * c)) ≃ Fin ((r * c) * a) :=
  (tripleRight r a c).trans ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)).trans
    ((Equiv.prodAssoc _ _ _).symm.trans (tripleLeft r c a).symm))

/-- Store the first output in the reference and expose the remaining input. -/
def storeOutput (r c b : ℕ) : Fin ((r * c) * b) ≃ Fin ((r * b) * c) :=
  (tripleLeft r c b).trans ((Equiv.prodAssoc _ _ _).trans
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)).trans
      ((Equiv.prodAssoc _ _ _).symm.trans (tripleLeft r b c).symm)))

/-- Restore the canonical reference/two-output coordinates. -/
def collect (r b d : ℕ) : Fin ((r * b) * d) ≃ Fin (r * (b * d)) :=
  (tripleLeft r b d).trans ((Equiv.prodAssoc _ _ _).trans (tripleRight r b d).symm)

def rightProduct (X : Operator r) (Y : Operator a) (Z : Operator c) : Operator (r * (a * c)) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (X ⊗ₖ Matrix.reindex finProdFinEquiv finProdFinEquiv (Y ⊗ₖ Z))

def leftProduct (X : Operator r) (Y : Operator a) (Z : Operator c) : Operator ((r * a) * c) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y) ⊗ₖ Z)

@[simp] theorem expose_product (X : Operator r) (Y : Operator a) (Z : Operator c) :
    Matrix.reindex (expose r a c) (expose r a c) (rightProduct X Y Z) = leftProduct X Z Y := by
  ext i j
  simp [rightProduct, leftProduct, expose, tripleLeft, tripleRight, Matrix.reindex_apply]
  ring

@[simp] theorem storeOutput_product (X : Operator r) (Z : Operator c) (Y : Operator b) :
    Matrix.reindex (storeOutput r c b) (storeOutput r c b) (leftProduct X Z Y) = leftProduct X Y Z := by
  ext i j
  simp [leftProduct, storeOutput, tripleLeft, Matrix.reindex_apply]
  ring

@[simp] theorem collect_product (X : Operator r) (Y : Operator b) (Z : Operator d) :
    Matrix.reindex (collect r b d) (collect r b d) (leftProduct X Y Z) = rightProduct X Y Z := by
  ext i j
  simp [rightProduct, leftProduct, collect, tripleLeft, tripleRight, Matrix.reindex_apply,
    mul_assoc]

/-- Five genuine local/control maps implement two independent channels serially. -/
def sequentialChannel (Φ : KrausChannel a b) (Ψ : KrausChannel c d) (r : ℕ) :
    KrausChannel (r * (a * c)) (r * (b * d)) :=
  (KrausChannel.coordinateChange (collect r b d)).compose
    (((KrausChannel.identity (r * b)).tensor Ψ).compose
      ((KrausChannel.coordinateChange (storeOutput r c b)).compose
        (((KrausChannel.identity (r * c)).tensor Φ).compose
          (KrausChannel.coordinateChange (expose r a c)))))

/-- Product matrix units (and indeed arbitrary product matrices) have the exact expected action. -/
theorem sequentialChannel_product (Φ : KrausChannel a b) (Ψ : KrausChannel c d)
    (X : Operator r) (Y : Operator a) (Z : Operator c) :
    (sequentialChannel Φ Ψ r).apply (rightProduct X Y Z) = rightProduct X (Φ.apply Y) (Ψ.apply Z) := by
  simp only [sequentialChannel, KrausChannel.compose_apply, KrausChannel.coordinateChange_apply,
    expose_product, leftProduct, KrausChannel.tensor_apply_product, KrausChannel.identity_apply]
  change Matrix.reindex (collect r b d) (collect r b d)
    (((KrausChannel.identity (r * b)).tensor Ψ).apply
      (Matrix.reindex (storeOutput r c b) (storeOutput r c b)
        (leftProduct X Z (Φ.apply Y)))) = _
  rw [storeOutput_product]
  simp only [leftProduct, KrausChannel.tensor_apply_product, KrausChannel.identity_apply]
  exact collect_product X (Φ.apply Y) (Ψ.apply Z)

/-- Equality of the actual matrix maps, including every entangled input. -/
theorem sequentialChannel_toLinearMap (Φ : KrausChannel a b) (Ψ : KrausChannel c d) (r : ℕ) :
    (sequentialChannel Φ Ψ r).toLinearMap =
      ((KrausChannel.identity r).tensor (Φ.tensor Ψ)).toLinearMap := by
  apply MatrixMap.choi_injective
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i,x⟩,rfl⟩ := (finProdFinEquiv (m := r) (n := a*c)).surjective i
  obtain ⟨⟨j,y⟩,rfl⟩ := (finProdFinEquiv (m := r) (n := a*c)).surjective j
  obtain ⟨⟨a₁,c₁⟩,rfl⟩ := (finProdFinEquiv (m := a) (n := c)).surjective x
  obtain ⟨⟨a₂,c₂⟩,rfl⟩ := (finProdFinEquiv (m := a) (n := c)).surjective y
  simp only [MatrixMap.choi, KrausChannel.toLinearMap]
  rw [← MatrixMap.reindex_product_single, ← MatrixMap.reindex_product_single]
  change (sequentialChannel Φ Ψ r).apply
    (rightProduct (Matrix.single i j 1) (Matrix.single a₁ a₂ 1) (Matrix.single c₁ c₂ 1)) u v =
    ((KrausChannel.identity r).tensor (Φ.tensor Ψ)).apply
      (rightProduct (Matrix.single i j 1) (Matrix.single a₁ a₂ 1) (Matrix.single c₁ c₂ 1)) u v
  rw [sequentialChannel_product]
  simp only [rightProduct, KrausChannel.tensor_apply_product, KrausChannel.identity_apply]

/-- State-level serial realization in the original canonical tensor coordinates. -/
theorem sequentialChannel_onState (Φ : KrausChannel a b) (Ψ : KrausChannel c d)
    (ρ : State (r * (a * c))) :
    (sequentialChannel Φ Ψ r).onState ρ = outputState (Φ.tensor Ψ) r ρ := by
  rw [ChannelLocality.outputState_eq_tensor]
  apply State.eq_of_matrix_eq
  exact congrArg (fun f : MatrixMap (r*(a*c)) (r*(b*d)) => f ρ.matrix)
    (sequentialChannel_toLinearMap Φ Ψ r)

end QuantumChannelStein.SequentialTensor
