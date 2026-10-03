import GeneralizedChannelStein.LiftedFamilies
import GeneralizedChannelStein.DimensionDomination

noncomputable section
namespace GeneralizedChannelStein.LiftedReplacerBound
open QuantumChannelStein Matrix
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {b e : ℕ}

/-- The auxiliary maximally-mixed factor loses exactly the scalar factor e. -/
theorem liftedReplacer_lower (ω : State b) (he : 0 < e) (w : ℝ)
    (hw : (ω.matrix-w • (1:Operator b)).PosSemidef) :
    ((liftedReplacer ω he).matrix-(w/(e:ℝ)) • (1:Operator (b*e))).PosSemidef := by
  have hp := MatrixMap.posSemidef_kronecker hw (FaithfulDensity.maximallyMixed e he).positive
  have hpr := hp.submatrix (finProdFinEquiv.symm)
  convert hpr using 1
  change Matrix.reindex finProdFinEquiv finProdFinEquiv
      (ω.matrix ⊗ₖ (FaithfulDensity.maximallyMixed e he).matrix) -
      (w/(e:ℝ)) • (1:Operator (b*e)) = _
  ext i j
  obtain ⟨⟨i,u⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j,v⟩,rfl⟩ := finProdFinEquiv.surjective j
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,
    Matrix.sub_apply,Matrix.kroneckerMap_apply,FaithfulDensity.maximallyMixed,
    Matrix.smul_apply,Complex.real_smul,Matrix.one_apply,
    finProdFinEquiv.injective.eq_iff,Prod.mk.injEq]
  split_ifs <;> simp_all [div_eq_mul_inv]
  all_goals ring

theorem lifted_scalar_pos {w : ℝ} (hw : 0 < w) (he : 0 < e) : 0 < w/(e:ℝ) :=
  div_pos hw (Nat.cast_pos.mpr he)

theorem liftedReplacer_minEigenvalue_lower (ω : State b) (hb : 0 < b)
    (hω : ω.matrix.PosDef) (he : 0 < e) :
    0 < DimensionDomination.minEigenvalue ω hb/(e:ℝ) ∧
    ((liftedReplacer ω he).matrix-
      (DimensionDomination.minEigenvalue ω hb/(e:ℝ)) • (1:Operator (b*e))).PosSemidef := by
  exact ⟨lifted_scalar_pos (DimensionDomination.minEigenvalue_pos ω hb hω) he,
    liftedReplacer_lower ω he _
      (DimensionDomination.scalar_le_of_eigenvalue_lower ω _ (DimensionDomination.minEigenvalue_le ω hb))⟩

end GeneralizedChannelStein.LiftedReplacerBound
