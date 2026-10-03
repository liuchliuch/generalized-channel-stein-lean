import GeneralizedChannelStein.TensorDiamond
import GeneralizedChannelStein.TraceNormProducts

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.GeneralTensorDiamond
open QuantumChannelStein DiamondNorm TraceNorm TensorDiamond
open scoped BigOperators Kronecker ComplexOrder
variable {a b c d : ℕ}

theorem amplify_smul (Q : MatrixMap a b) (r : ℕ)
    (z : ℂ) (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    MatrixMap.amplify Q r (z • X) = z • MatrixMap.amplify Q r X := by
  ext ⟨i,j⟩ ⟨k,l⟩
  change Q (z • (fun u v => X (i,u) (k,v))) j l = _
  rw [map_smul]
  rfl

/-- Homogeneous estimate for every complex input matrix and every reference dimension. -/
theorem amplify_norm_le (Q : MatrixMap a b) (r : ℕ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    ENNReal.ofReal (traceNorm (MatrixMap.amplify Q r X)) ≤
      diamondNorm Q * ENNReal.ofReal (traceNorm X) := by
  by_cases hX : X=0
  · subst X
    have hz : MatrixMap.amplify Q r 0=0 := by ext ⟨i,j⟩ ⟨k,l⟩; exact congrFun (congrFun (map_zero Q) j) l
    simp [hz, traceNorm_eq_matrixTraceNorm]
  have ht : 0<traceNorm X := lt_of_le_of_ne (traceNorm_nonneg X)
    (Ne.symm (fun hz => hX ((Matrix.traceNorm_zero_iff X).mp hz)))
  let Y := (((traceNorm X)⁻¹:ℝ):ℂ) • X
  have hY : traceNorm Y≤1 := by
    dsimp [Y]
    rw [traceNorm_real_smul, abs_of_pos (inv_pos.mpr ht), inv_mul_cancel₀ ht.ne']
  have hXY : X=((traceNorm X:ℝ):ℂ) • Y := by
    dsimp [Y]
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hout : MatrixMap.amplify Q r X =
      ((traceNorm X:ℝ):ℂ) • MatrixMap.amplify Q r Y := by
    conv_lhs => rw [hXY]
    exact amplify_smul Q r _ Y
  rw [hout,traceNorm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,
    ENNReal.ofReal_mul ht.le,mul_comm]
  have hb : ENNReal.ofReal (traceNorm (MatrixMap.amplify Q r Y)) ≤ diamondNorm Q :=
    le_iSup_of_le r (le_iSup_of_le (⟨Y,hY⟩ : {Y // traceNorm Y≤1}) le_rfl)
  exact mul_le_mul_right' hb _

/-- Submultiplicativity under composition for arbitrary linear maps. -/
theorem diamondNorm_comp_le (P : MatrixMap b c) (Q : MatrixMap a b) :
    diamondNorm (P.comp Q) ≤ diamondNorm P*diamondNorm Q := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  rw [PostprocessingBounds.amplify_comp]
  have hb : ENNReal.ofReal (traceNorm (MatrixMap.amplify Q r X.val)) ≤ diamondNorm Q :=
    le_iSup_of_le r (le_iSup_of_le X le_rfl)
  exact (amplify_norm_le P r _).trans (mul_le_mul_left' hb _)

theorem tensor_apply_product (P : MatrixMap a b) (Q : MatrixMap c d)
    (X : Operator a) (Y : Operator c) :
    MatrixMap.tensor P Q (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y)) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (P X ⊗ₖ Q Y) := by
  conv_rhs => rw [MatrixMap.apply_eq_sum P X, MatrixMap.apply_eq_sum Q Y]
  ext i j
  simp only [MatrixMap.tensor, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem tensor_factor (P : MatrixMap a b) (Q : MatrixMap c d) :
    MatrixMap.tensor P Q =
      (MatrixMap.tensor P (KrausChannel.identity d).toLinearMap).comp (extend a Q) := by
  rw [extend_eq_tensor]
  apply MatrixMap.choi_injective
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i,k⟩,rfl⟩ := (finProdFinEquiv (m:=a) (n:=c)).surjective i
  obtain ⟨⟨j,l⟩,rfl⟩ := (finProdFinEquiv (m:=a) (n:=c)).surjective j
  simp only [MatrixMap.choi, LinearMap.comp_apply, MatrixMap.tensor_single]
  rw [tensor_apply_product]
  simp only [KrausChannel.toLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    KrausChannel.identity_apply]

/-- Arbitrary linear maps satisfy tensor submultiplicativity of the full diamond norm. -/
theorem diamondNorm_tensor_le (P : MatrixMap a b) (Q : MatrixMap c d) :
    diamondNorm (MatrixMap.tensor P Q) ≤ diamondNorm P*diamondNorm Q := by
  rw [tensor_factor]
  exact (diamondNorm_comp_le _ _).trans (mul_le_mul'
    (diamondNorm_tensor_channel_right _ _) (diamondNorm_extend_le _ _))

theorem amplify_tensor_product (P : MatrixMap a b) (Q : MatrixMap c d) (r s : ℕ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ)
    (Y : Matrix (Fin s × Fin c) (Fin s × Fin c) ℂ) :
    MatrixMap.amplify (MatrixMap.tensor P Q) (r*s)
      (Matrix.reindex (MatrixMap.choiShuffle r a s c) (MatrixMap.choiShuffle r a s c) (X ⊗ₖ Y)) =
    Matrix.reindex (MatrixMap.choiShuffle r b s d) (MatrixMap.choiShuffle r b s d)
      (MatrixMap.amplify P r X ⊗ₖ MatrixMap.amplify Q s Y) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i,k⟩,rfl⟩ := (finProdFinEquiv (m:=r) (n:=s)).surjective i
  obtain ⟨⟨j,l⟩,rfl⟩ := (finProdFinEquiv (m:=r) (n:=s)).surjective j
  obtain ⟨⟨u,w⟩,rfl⟩ := (finProdFinEquiv (m:=b) (n:=d)).surjective u
  obtain ⟨⟨v,x⟩,rfl⟩ := (finProdFinEquiv (m:=b) (n:=d)).surjective v
  have h := tensor_apply_product P Q (fun u v => X (i,u) (j,v)) (fun w x => Y (k,w) (l,x))
  have hh := congrFun (congrFun h (finProdFinEquiv (u,w))) (finProdFinEquiv (v,x))
  simpa only [MatrixMap.amplify, MatrixMap.choiShuffle, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kroneckerMap_apply] using hh

/-- Product inputs witness the reverse bound; each input may itself be reference-entangled. -/
theorem diamondNorm_mul_le_tensor (P : MatrixMap a b) (Q : MatrixMap c d) :
    diamondNorm P*diamondNorm Q ≤ diamondNorm (MatrixMap.tensor P Q) := by
  conv_lhs => unfold diamondNorm
  rw [ENNReal.iSup_mul]
  apply iSup_le
  intro r
  rw [ENNReal.iSup_mul]
  apply iSup_le
  intro X
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro s
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro Y
  let Z := Matrix.reindex (MatrixMap.choiShuffle r a s c) (MatrixMap.choiShuffle r a s c)
    (X.val ⊗ₖ Y.val)
  have hZ : traceNorm Z≤1 := by
    unfold Z
    rw [traceNorm_reindex,traceNorm_kronecker]
    exact (mul_le_mul X.property Y.property (traceNorm_nonneg _) (by norm_num)).trans (by norm_num)
  have hh : ENNReal.ofReal (traceNorm (MatrixMap.amplify (MatrixMap.tensor P Q) (r*s) Z)) ≤
      diamondNorm (MatrixMap.tensor P Q) :=
    le_iSup_of_le (r*s) (le_iSup_of_le (⟨Z,hZ⟩ : {Z // traceNorm Z≤1}) le_rfl)
  unfold Z at hh
  rw [amplify_tensor_product,traceNorm_reindex,traceNorm_kronecker,
    ENNReal.ofReal_mul (traceNorm_nonneg _)] at hh
  exact hh

/-- Exact multiplicativity of the full diamond norm for all complex-linear matrix maps. -/
theorem diamondNorm_tensor (P : MatrixMap a b) (Q : MatrixMap c d) :
    diamondNorm (MatrixMap.tensor P Q) = diamondNorm P*diamondNorm Q :=
  le_antisymm (diamondNorm_tensor_le P Q) (diamondNorm_mul_le_tensor P Q)

/-- Tensoring any matrix map with a channel preserves its full diamond norm exactly. -/
theorem diamondNorm_tensor_channel (P : MatrixMap a b) (Q : KrausChannel c d) (hc : 0<c) :
    diamondNorm (MatrixMap.tensor P Q.toLinearMap) = diamondNorm P := by
  rw [diamondNorm_tensor, diamondNorm_channel Q hc, mul_one]

theorem diamondNorm_channel_tensor (P : KrausChannel a b) (Q : MatrixMap c d) (ha : 0<a) :
    diamondNorm (MatrixMap.tensor P.toLinearMap Q) = diamondNorm Q := by
  rw [diamondNorm_tensor, diamondNorm_channel P ha, one_mul]

end GeneralizedChannelStein.GeneralTensorDiamond
