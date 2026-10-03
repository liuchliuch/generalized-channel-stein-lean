import GeneralizedChannelStein.CovariantFamilies
import GeneralizedChannelStein.PostprocessingBounds
import GeneralizedChannelStein.TraceDefectCompletion
import QuantumChannelStein.TraceNormCoordinates
import QuantumChannelStein.TensorMap
import QuantumChannelStein.ChannelPowerReindex

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.TensorDiamond
open QuantumChannelStein DiamondNorm TraceNorm
open scoped BigOperators Kronecker ComplexOrder
variable {a b a' b' : ℕ}

/-- Literal input/output coordinate transport of an arbitrary matrix map. -/
def reindexMap (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (Q : MatrixMap a b) : MatrixMap a' b' :=
  (Matrix.reindexLinearEquiv ℂ ℂ eb eb).toLinearMap.comp
    (Q.comp (Matrix.reindexLinearEquiv ℂ ℂ ea.symm ea.symm).toLinearMap)

theorem amplify_reindexMap (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (Q : MatrixMap a b) (r : ℕ)
    (X : Matrix (Fin r × Fin a') (Fin r × Fin a') ℂ) :
    MatrixMap.amplify (reindexMap ea eb Q) r X =
      Matrix.reindex (Equiv.prodCongr (Equiv.refl _) eb)
        (Equiv.prodCongr (Equiv.refl _) eb)
        (MatrixMap.amplify Q r
          (Matrix.reindex (Equiv.prodCongr (Equiv.refl _) ea.symm)
            (Equiv.prodCongr (Equiv.refl _) ea.symm) X)) := by
  rfl

/-- Coordinate changes preserve the full diamond bound, without restrictions on inputs. -/
theorem diamondNorm_reindexMap_le (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (Q : MatrixMap a b) : diamondNorm (reindexMap ea eb Q) ≤ diamondNorm Q := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  rw [amplify_reindexMap, traceNorm_reindex]
  let Y := Matrix.reindex (Equiv.prodCongr (Equiv.refl (Fin r)) ea.symm)
    (Equiv.prodCongr (Equiv.refl (Fin r)) ea.symm) X.val
  have hY : traceNorm Y ≤ 1 := by
    simpa only [Y, traceNorm_reindex] using X.property
  exact le_iSup_of_le r (le_iSup_of_le (⟨Y,hY⟩ : {Y // traceNorm Y ≤ 1}) le_rfl)

/-- Identity reference extension, in flattened finite coordinates. -/
def extend (s : ℕ) (Q : MatrixMap a b) : MatrixMap (s*a) (s*b) where
  toFun X := Matrix.reindex finProdFinEquiv finProdFinEquiv
    (MatrixMap.amplify Q s (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm X))
  map_add' X Y := by
    ext i j
    change Q ((fun k l => X (finProdFinEquiv ((finProdFinEquiv.symm i).1,k))
      (finProdFinEquiv ((finProdFinEquiv.symm j).1,l))) +
      (fun k l => Y (finProdFinEquiv ((finProdFinEquiv.symm i).1,k))
      (finProdFinEquiv ((finProdFinEquiv.symm j).1,l)))) _ _ = _
    rw [map_add]; rfl
  map_smul' c X := by
    ext i j
    change Q (c • (fun k l => X (finProdFinEquiv ((finProdFinEquiv.symm i).1,k))
      (finProdFinEquiv ((finProdFinEquiv.symm j).1,l)))) _ _ = _
    rw [map_smul]; rfl

/-- Reassociate an arbitrary external reference with the added reference. -/
def referenceAssoc (r s a : ℕ) : (Fin r × Fin (s*a)) ≃ (Fin (r*s) × Fin a) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm).trans
    ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)))

theorem amplify_extend (s : ℕ) (Q : MatrixMap a b) (r : ℕ)
    (X : Matrix (Fin r × Fin (s*a)) (Fin r × Fin (s*a)) ℂ) :
    MatrixMap.amplify (extend s Q) r X =
      Matrix.reindex (referenceAssoc r s b).symm (referenceAssoc r s b).symm
        (MatrixMap.amplify Q (r*s)
          (Matrix.reindex (referenceAssoc r s a) (referenceAssoc r s a) X)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [extend, MatrixMap.amplify, referenceAssoc, Matrix.reindex_apply,
    Matrix.submatrix_apply]

/-- Adding an identity reference cannot increase the full diamond norm. -/
theorem diamondNorm_extend_le (s : ℕ) (Q : MatrixMap a b) :
    diamondNorm (extend s Q) ≤ diamondNorm Q := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  rw [amplify_extend, traceNorm_reindex]
  let Y := Matrix.reindex (referenceAssoc r s a) (referenceAssoc r s a) X.val
  have hY : traceNorm Y ≤ 1 := by simpa only [Y, traceNorm_reindex] using X.property
  exact le_iSup_of_le (r*s) (le_iSup_of_le (⟨Y,hY⟩ : {Y // traceNorm Y ≤ 1}) le_rfl)

/-- The extension is the literal tensor product with an identity channel. -/
theorem extend_eq_tensor (s : ℕ) (Q : MatrixMap a b) :
    extend s Q = MatrixMap.tensor (KrausChannel.identity s).toLinearMap Q := by
  apply MatrixMap.choi_injective
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i,k⟩,rfl⟩ := (finProdFinEquiv (m:=s) (n:=a)).surjective i
  obtain ⟨⟨j,l⟩,rfl⟩ := (finProdFinEquiv (m:=s) (n:=a)).surjective j
  obtain ⟨⟨u,w⟩,rfl⟩ := (finProdFinEquiv (m:=s) (n:=b)).surjective u
  obtain ⟨⟨v,x⟩,rfl⟩ := (finProdFinEquiv (m:=s) (n:=b)).surjective v
  simp only [MatrixMap.choi, MatrixMap.tensor_single, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kronecker_apply]
  simp only [extend, LinearMap.coe_mk, AddHom.coe_mk, MatrixMap.amplify, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  change Q (fun k' l' => Matrix.single (finProdFinEquiv (i,k))
    (finProdFinEquiv (j,l)) 1 (finProdFinEquiv (u,k')) (finProdFinEquiv (v,l'))) w x = _
  simp only [KrausChannel.toLinearMap, LinearMap.coe_mk, AddHom.coe_mk, KrausChannel.identity_apply]
  by_cases hi : i=u <;> by_cases hj : j=v
  · subst u; subst v
    have hf : (fun k' l' : Fin a => Matrix.single (finProdFinEquiv (i,k))
        (finProdFinEquiv (j,l)) (1:ℂ) (finProdFinEquiv (i,k'))
        (finProdFinEquiv (j,l'))) = Matrix.single k l 1 := by
      ext k' l'
      simp [Matrix.single, finProdFinEquiv.injective.eq_iff]
    rw [hf]
    simp [Matrix.single]
  · have hz : (fun k' l' : Fin a => Matrix.single (finProdFinEquiv (i,k))
        (finProdFinEquiv (j,l)) (1:ℂ) (finProdFinEquiv (u,k'))
        (finProdFinEquiv (v,l'))) = 0 := by
      ext k' l'; simp [Matrix.single, finProdFinEquiv.injective.eq_iff, hj]
    rw [hz, map_zero]
    simp [Matrix.single, hj]
  · have hz : (fun k' l' : Fin a => Matrix.single (finProdFinEquiv (i,k))
        (finProdFinEquiv (j,l)) (1:ℂ) (finProdFinEquiv (u,k'))
        (finProdFinEquiv (v,l'))) = 0 := by
      ext k' l'; simp [Matrix.single, finProdFinEquiv.injective.eq_iff, hi]
    rw [hz, map_zero]
    simp [Matrix.single, hi]
  · have hz : (fun k' l' : Fin a => Matrix.single (finProdFinEquiv (i,k))
        (finProdFinEquiv (j,l)) (1:ℂ) (finProdFinEquiv (u,k'))
        (finProdFinEquiv (v,l'))) = 0 := by
      ext k' l'; simp [Matrix.single, finProdFinEquiv.injective.eq_iff, hi]
    rw [hz, map_zero]
    simp [Matrix.single, hi]

theorem tensor_left_postcompose {c d : ℕ} (P : KrausChannel a b) (Q : MatrixMap c d) :
    MatrixMap.tensor P.toLinearMap Q =
      (P.tensor (KrausChannel.identity d)).toLinearMap.comp (extend a Q) := by
  rw [extend_eq_tensor]
  apply MatrixMap.choi_injective
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i,k⟩,rfl⟩ := (finProdFinEquiv (m:=a) (n:=c)).surjective i
  obtain ⟨⟨j,l⟩,rfl⟩ := (finProdFinEquiv (m:=a) (n:=c)).surjective j
  simp only [MatrixMap.choi, LinearMap.comp_apply, MatrixMap.tensor_single]
  change _ = (P.tensor (KrausChannel.identity d)).apply _ u v
  rw [KrausChannel.tensor_apply_product]
  simp only [KrausChannel.toLinearMap, LinearMap.coe_mk, AddHom.coe_mk, KrausChannel.identity_apply]

theorem diamondNorm_tensor_channel_left {c d : ℕ} (P : KrausChannel a b)
    (Q : MatrixMap c d) : diamondNorm (MatrixMap.tensor P.toLinearMap Q) ≤ diamondNorm Q := by
  rw [tensor_left_postcompose]
  exact (PostprocessingBounds.diamondNorm_postcompose _ _).trans (diamondNorm_extend_le _ _)

def swapFin (a c : ℕ) : Fin (a*c) ≃ Fin (c*a) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

@[simp] theorem swapFin_apply (i : Fin a) (j : Fin b) :
    swapFin a b (finProdFinEquiv (i,j)) = finProdFinEquiv (j,i) := by
  simp [swapFin]

@[simp] theorem swapFin_symm_apply (i : Fin a) (j : Fin b) :
    (swapFin b a).symm (finProdFinEquiv (i,j)) = finProdFinEquiv (j,i) := by
  simp [swapFin]

theorem tensor_swap {c d : ℕ} (P : MatrixMap a b) (Q : MatrixMap c d) :
    reindexMap (swapFin a c) (swapFin b d) (MatrixMap.tensor P Q) =
      MatrixMap.tensor Q P := by
  apply MatrixMap.choi_injective
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i,k⟩,rfl⟩ := (finProdFinEquiv (m:=c) (n:=a)).surjective i
  obtain ⟨⟨j,l⟩,rfl⟩ := (finProdFinEquiv (m:=c) (n:=a)).surjective j
  obtain ⟨⟨u,w⟩,rfl⟩ := (finProdFinEquiv (m:=d) (n:=b)).surjective u
  obtain ⟨⟨v,x⟩,rfl⟩ := (finProdFinEquiv (m:=d) (n:=b)).surjective v
  simp only [MatrixMap.choi, reindexMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Matrix.reindexLinearEquiv_apply,
    ChannelPowerReindex.reindex_single, swapFin_symm_apply,
    MatrixMap.tensor_single, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.kronecker_apply]
  have hs := ChannelPowerReindex.reindex_single (swapFin a c).symm
    (finProdFinEquiv (i,k)) (finProdFinEquiv (j,l))
  simp only [swapFin_symm_apply] at hs
  change (MatrixMap.tensor P Q (Matrix.reindex (swapFin a c).symm (swapFin a c).symm
    (Matrix.single (finProdFinEquiv (i,k)) (finProdFinEquiv (j,l)) 1)))
    (finProdFinEquiv (w,u)) (finProdFinEquiv (x,v)) = _
  rw [hs, MatrixMap.tensor_single]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kronecker_apply]
  exact mul_comm _ _

theorem diamondNorm_tensor_channel_right {c d : ℕ} (P : MatrixMap a b)
    (Q : KrausChannel c d) : diamondNorm (MatrixMap.tensor P Q.toLinearMap) ≤ diamondNorm P := by
  rw [← tensor_swap Q.toLinearMap P]
  exact (diamondNorm_reindexMap_le _ _ _).trans (diamondNorm_tensor_channel_left _ _)

/-- Full diamond error of product channels, valid for arbitrary entangled references and inputs. -/
theorem tensor_channel_difference_le {c d : ℕ} (P P' : KrausChannel a b)
    (Q Q' : KrausChannel c d) :
    diamondNorm ((P.tensor Q).toLinearMap-(P'.tensor Q').toLinearMap) ≤
      diamondNorm (P.toLinearMap-P'.toLinearMap)+diamondNorm (Q.toLinearMap-Q'.toLinearMap) := by
  have he : (P.tensor Q).toLinearMap-(P'.tensor Q').toLinearMap =
      MatrixMap.tensor (P.toLinearMap-P'.toLinearMap) Q.toLinearMap +
      MatrixMap.tensor P'.toLinearMap (Q.toLinearMap-Q'.toLinearMap) := by
    rw [MatrixMap.tensor_sub_left, MatrixMap.tensor_sub_right]
    simp only [MatrixMap.tensor_kraus_toLinearMap]
    abel
  rw [he]
  exact (TraceDefectCompletion.diamondNorm_add_le _ _).trans
    (add_le_add (diamondNorm_tensor_channel_right _ _) (diamondNorm_tensor_channel_left _ _))

@[simp] theorem reindexMap_sub (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P Q : MatrixMap a b) : reindexMap ea eb (P-Q) = reindexMap ea eb P-reindexMap ea eb Q := by
  ext X i j
  rfl

@[simp] theorem reindexMap_smul (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (z : ℂ) (P : MatrixMap a b) : reindexMap ea eb (z • P) = z • reindexMap ea eb P := by
  ext X i j
  rfl

theorem reindexMap_channel (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P : KrausChannel a b) : reindexMap ea eb P.toLinearMap =
      (ChannelPowerReindex.reindexChannel ea eb P).toLinearMap := by
  ext X i j
  exact congrFun (congrFun (reindexChannel_apply_any ea eb P X).symm i) j

theorem cpLe_reindexMap (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    {P Q : MatrixMap a b} (h : MatrixMap.CPLe P Q) :
    MatrixMap.CPLe (reindexMap ea eb P) (reindexMap ea eb Q) := by
  change MatrixMap.CompletelyPositive _
  rw [← reindexMap_sub]
  intro r X hX
  rw [amplify_reindexMap]
  exact (h r _ (hX.submatrix _)).submatrix _

theorem tensorBlocks_difference_le (n m : ℕ)
    (P P' : KrausChannel (a^n) (b^n)) (Q Q' : KrausChannel (a^m) (b^m)) :
    diamondNorm ((tensorBlocks n m P Q).toLinearMap-(tensorBlocks n m P' Q').toLinearMap) ≤
      diamondNorm (P.toLinearMap-P'.toLinearMap)+diamondNorm (Q.toLinearMap-Q'.toLinearMap) := by
  simp only [tensorBlocks, ← reindexMap_channel, ← reindexMap_sub]
  exact (diamondNorm_reindexMap_le _ _ _).trans (tensor_channel_difference_le _ _ _ _)

end GeneralizedChannelStein.TensorDiamond
