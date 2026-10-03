import GeneralizedChannelStein.DiscardedBranch
import GeneralizedChannelStein.CloseBranchCompletion

/-! Padding exact isometry sites before trace-preserving completion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CompletionPadding
open QuantumChannelStein Matrix ChannelPowerReindex ChannelTransport BranchExtraction
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b c d : ℕ}

theorem adMap_tensor (V : Matrix (Fin b) (Fin a) ℂ) (W : Matrix (Fin d) (Fin c) ℂ) :
    MatrixMap.tensor (adMap V) (adMap W)=adMap (Matrix.reindex finProdFinEquiv finProdFinEquiv (V ⊗ₖ W)) := by
  apply MatrixMap.choi_injective
  ext ⟨i,x⟩ ⟨j,y⟩
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨x1,x2⟩,rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨y1,y2⟩,rfl⟩ := finProdFinEquiv.surjective y
  change MatrixMap.tensor (adMap V) (adMap W) (Matrix.single _ _ 1) _ _=_
  rw [MatrixMap.tensor_single]
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply,Matrix.kroneckerMap_apply]
  change MatrixMap.choi (adMap V) (i1,x1) (j1,y1)*MatrixMap.choi (adMap W) (i2,x2) (j2,y2)=_
  simp [LocalChoiDomination.choi_adMap_apply,Matrix.reindex_apply,Matrix.kroneckerMap_apply,map_mul]
  ring

def pad {a d : ℕ} (J : Matrix (Fin d) (Fin a) ℂ) (k m : ℕ)
    (Z : Matrix (Fin (d^k)) (Fin (a^k)) ℂ) : Matrix (Fin (d^(k+m))) (Fin (a^(k+m))) ℂ :=
  Matrix.reindex (channelAddEquiv d k m) (channelAddEquiv a k m)
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (Z ⊗ₖ powerIsometry J m))

theorem pad_target {a d : ℕ} (J : Matrix (Fin d) (Fin a) ℂ) (k m : ℕ) :
    pad J k m (powerIsometry J k)=powerIsometry J (k+m) := by
  rw [pad,← DiscardedBranch.powerIsometry_add]
  ext i j
  simp [Matrix.reindex_apply,Matrix.submatrix_submatrix]

theorem pad_error {a d : ℕ} (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (k m : ℕ) (Z : Matrix (Fin (d^k)) (Fin (a^k)) ℂ) :
    ‖pad J k m Z-powerIsometry J (k+m)‖≤‖Z-powerIsometry J k‖ := by
  rw [← pad_target J k m]
  have he : pad J k m Z-pad J k m (powerIsometry J k)=pad J k m (Z-powerIsometry J k) := by
    ext i j
    simp [pad,Matrix.reindex_apply,Matrix.kroneckerMap_apply,sub_mul]
  rw [he,pad,TensorPower.norm_reindex,TensorPower.norm_reindex]
  exact (TensorAlgebra.kronecker_opNorm_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (BranchExtraction.norm_isometry_le_one _ (powerIsometry_isometry J hJ m)))

theorem isometry_replacer_power {a d : ℕ} (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (ω : State d) (w : ℝ) (hw : 0<w) (hω : (ω.matrix-w•(1:Operator d)).PosSemidef) (m : ℕ) :
    MatrixMap.CPLe (adMap (powerIsometry J m))
      (Complex.ofReal (((d:ℝ)/w)^m)•((ReplacerChannel.channel a ω).tensorPower m).toLinearMap) := by
  have h := KrausChannel.cpLe_tensorPower (GeneralizedChannelStein.isometryChannel J hJ)
    (ReplacerChannel.channel a ω) (by positivity : 0≤(d:ℝ)/w)
    (DimensionDomination.cpLe_replacer_of_lower_bound (GeneralizedChannelStein.isometryChannel J hJ) ω w hw hω) m
  rw [isometryChannel_power_map] at h
  exact h

theorem pad_dominated {a d : ℕ} (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (F : AlternativeFamily a d) (hF : Admissible F) (ω : State d)
    (hωmem : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (w : ℝ) (hw : 0<w) (hω : (ω.matrix-w•(1:Operator d)).PosSemidef)
    (k m : ℕ) (hk : 0<k) (hm : 0<m) (M : KrausChannel (a^k) (d^k)) (hM : M.toLinearMap∈F k)
    (Z : Matrix (Fin (d^k)) (Fin (a^k)) ℂ) (s : ℝ) (hs : 0≤s)
    (hdom : MatrixMap.CPLe (adMap Z) (Complex.ofReal s•M.toLinearMap)) :
    ∃ S : KrausChannel (a^(k+m)) (d^(k+m)), S.toLinearMap∈F (k+m) ∧
      MatrixMap.CPLe (adMap (pad J k m Z)) (Complex.ofReal (s*((d:ℝ)/w)^m)•S.toLinearMap) := by
  let R := (ReplacerChannel.channel a ω).tensorPower m
  let S := tensorBlocks k m M R
  have hR : R.toLinearMap∈F m := replacer_power_mem F hF.tensor_closed ω hωmem m hm
  refine ⟨S,hF.tensor_closed k m hk hm M R hM hR,?_⟩
  have ht := MatrixMap.cpLe_tensor (MatrixMap.completelyPositive_ofKraus (fun _ : Fin 1 => Z))
    (MatrixMap.completelyPositive_smul (by positivity : 0≤((d:ℝ)/w)^m)
      (MatrixMap.completelyPositive_toLinearMap R)) hdom (isometry_replacer_power J hJ ω w hw hω m)
  change MatrixMap.CPLe (MatrixMap.tensor (adMap Z) (adMap (powerIsometry J m))) _ at ht
  rw [adMap_tensor,MatrixMap.tensor_smul_left,MatrixMap.tensor_smul_right,smul_smul,
    ← Complex.ofReal_mul,MatrixMap.tensor_kraus_toLinearMap] at ht
  have hh := reindexMap_cpLe (channelAddEquiv a k m) (channelAddEquiv d k m) _ _ ht
  simpa only [FreeMultipliers.reindexMap_adMap,reindexMap_smul,← reindexChannel_map] using hh

end GeneralizedChannelStein.CompletionPadding
