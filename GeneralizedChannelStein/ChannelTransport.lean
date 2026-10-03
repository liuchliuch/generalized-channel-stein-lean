import GeneralizedChannelStein.TraceDefectCompletion

/-! # Coordinate transport of actual maps, CP order and full diamond norm -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.ChannelTransport
open QuantumChannelStein Matrix ChannelPowerReindex DiamondNorm
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b a' b' : ℕ}

def reindexMap (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b') (P : MatrixMap a b) : MatrixMap a' b' :=
  (Matrix.reindexLinearEquiv ℂ ℂ eb eb).toLinearMap.comp
    (P.comp (Matrix.reindexLinearEquiv ℂ ℂ ea.symm ea.symm).toLinearMap)

@[simp] theorem reindexMap_apply (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P : MatrixMap a b) (X : Operator a') :
    reindexMap ea eb P X = Matrix.reindex eb eb (P (Matrix.reindex ea.symm ea.symm X)) := rfl

theorem amplify_reindexMap (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P : MatrixMap a b) (r : ℕ)
    (X : Matrix (Fin r × Fin a') (Fin r × Fin a') ℂ) :
    MatrixMap.amplify (reindexMap ea eb P) r X =
      Matrix.reindex (Equiv.prodCongr (Equiv.refl (Fin r)) eb)
        (Equiv.prodCongr (Equiv.refl (Fin r)) eb)
        (MatrixMap.amplify P r (Matrix.reindex
          (Equiv.prodCongr (Equiv.refl (Fin r)) ea.symm)
          (Equiv.prodCongr (Equiv.refl (Fin r)) ea.symm) X)) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  rfl

theorem diamondNorm_reindexMap_le (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P : MatrixMap a b) : diamondNorm (reindexMap ea eb P) ≤ diamondNorm P := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  rw [amplify_reindexMap, TraceNorm.traceNorm_reindex]
  apply le_iSup_of_le r
  let Y := Matrix.reindex (Equiv.prodCongr (Equiv.refl (Fin r)) ea.symm)
    (Equiv.prodCongr (Equiv.refl (Fin r)) ea.symm) X.val
  have hY : TraceNorm.traceNorm Y ≤ 1 := by
    dsimp only [Y]
    rw [TraceNorm.traceNorm_reindex]
    exact X.property
  exact le_iSup_of_le ⟨Y,hY⟩ le_rfl

@[simp] theorem reindexMap_inverse (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P : MatrixMap a b) : reindexMap ea.symm eb.symm (reindexMap ea eb P) = P := by
  ext X i j
  simp [reindexMap_apply, Matrix.reindex_apply, Matrix.submatrix_submatrix]

theorem diamondNorm_reindexMap (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P : MatrixMap a b) : diamondNorm (reindexMap ea eb P) = diamondNorm P := by
  apply le_antisymm (diamondNorm_reindexMap_le ea eb P)
  simpa using diamondNorm_reindexMap_le ea.symm eb.symm (reindexMap ea eb P)

theorem reindexMap_cp (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P : MatrixMap a b) (hP : MatrixMap.CompletelyPositive P) :
    MatrixMap.CompletelyPositive (reindexMap ea eb P) := by
  intro r X hX
  rw [amplify_reindexMap]
  exact (hP r _ (hX.submatrix _)).submatrix _

@[simp] theorem reindexMap_sub (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P Q : MatrixMap a b) : reindexMap ea eb (P-Q) = reindexMap ea eb P - reindexMap ea eb Q := by
  ext X i j
  rfl

@[simp] theorem reindexMap_smul (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P : MatrixMap a b) (c : ℂ) : reindexMap ea eb (c • P) = c • reindexMap ea eb P := by
  ext X i j
  rfl

theorem reindexMap_cpLe (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P Q : MatrixMap a b) (h : MatrixMap.CPLe P Q) :
    MatrixMap.CPLe (reindexMap ea eb P) (reindexMap ea eb Q) := by
  have h' := reindexMap_cp ea eb (Q-P) h
  simpa only [reindexMap_sub] using h'

theorem reindexChannel_map (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (P : KrausChannel a b) : (reindexChannel ea eb P).toLinearMap = reindexMap ea eb P.toLinearMap := by
  ext X i j
  have h := reindexChannel_apply ea eb P (Matrix.reindex ea.symm ea.symm X)
  simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix] using congrFun (congrFun h i) j

theorem reindexMap_trans {a'' b'' : ℕ}
    (ea : Fin a≃Fin a') (eb : Fin b≃Fin b')
    (fa : Fin a'≃Fin a'') (fb : Fin b'≃Fin b'') (P : MatrixMap a b) :
    reindexMap fa fb (reindexMap ea eb P)=reindexMap (ea.trans fa) (eb.trans fb) P := rfl

end GeneralizedChannelStein.ChannelTransport
