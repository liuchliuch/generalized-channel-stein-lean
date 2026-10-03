import GeneralizedChannelStein.CovariantFamilies

/-! Positive partial transpose on the entire output of a correlated block channel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelPowerReindex PerfectDiscrimination Matrix TestingSDP
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- Output partial transpose: the reference index is never transposed. -/
def partialTranspose (C : BipartiteOperator a b) : BipartiteOperator a b :=
  fun i j => C (i.1,j.2) (j.1,i.2)

/-- Ordinary transpose as a complex-linear map, without conjugation. -/
def transposeMap (d : ℕ) : MatrixMap d d where
  toFun X := X.transpose
  map_add' X Y := Matrix.transpose_add X Y
  map_smul' c X := Matrix.transpose_smul c X

theorem choi_transpose_comp (Φ : MatrixMap a b) :
    MatrixMap.choi ((transposeMap b).comp Φ) = partialTranspose (MatrixMap.choi Φ) := rfl

theorem completelyPositive_comp {c : ℕ} {Φ : MatrixMap a b} {Ψ : MatrixMap b c}
    (hΦ : MatrixMap.CompletelyPositive Φ) (hΨ : MatrixMap.CompletelyPositive Ψ) :
    MatrixMap.CompletelyPositive (Ψ.comp Φ) := by
  intro r X hX
  exact hΨ r (MatrixMap.amplify Φ r X) (hΦ r X hX)

/-- PPT is equivalent to complete positivity after output transposition. -/
def IsPPT (Φ : MatrixMap a b) : Prop := (partialTranspose (MatrixMap.choi Φ)).PosSemidef

theorem isPPT_iff_transpose_comp_cp (Φ : MatrixMap a b) :
    IsPPT Φ ↔ MatrixMap.CompletelyPositive ((transposeMap b).comp Φ) := by
  rw [MatrixMap.completelyPositive_iff_choi_positive,choi_transpose_comp]
  rfl

def PPTFamily (a b : ℕ) : AlternativeFamily a b := fun n =>
  {Φ | IsChannel Φ ∧ IsPPT Φ}

theorem continuous_partialTranspose : Continuous (@partialTranspose a b) := by
  unfold partialTranspose
  fun_prop

theorem partialTranspose_mix (C D : BipartiteOperator a b) (r s : ℝ) :
    partialTranspose (r • C+s • D) = r • partialTranspose C+s • partialTranspose D := rfl

theorem ppt_choi_image (a b n : ℕ) :
    MatrixMap.choi '' PPTFamily a b n = channelChoiSet (a^n) (b^n) ∩
      {C | (partialTranspose C).PosSemidef} := by
  apply channelSlice_choi_image
  intro Φ; rfl

theorem isClosed_pptChoi (a b : ℕ) :
    IsClosed {C : BipartiteOperator a b | (partialTranspose C).PosSemidef} := by
  letI : CStarAlgebra (BipartiteOperator a b) := CStarAlgebra.mk
  have h : IsClosed {C : BipartiteOperator a b | (0:BipartiteOperator a b) ≤ partialTranspose C} :=
    isClosed_le continuous_const (continuous_partialTranspose (a:=a) (b:=b))
  simpa only [Matrix.nonneg_iff_posSemidef] using h

theorem convex_pptChoi (a b : ℕ) : Convex ℝ {C : BipartiteOperator a b | (partialTranspose C).PosSemidef} := by
  intro C hC D hD r s hr hs hrs
  exact (hC.smul hr).add (hD.smul hs)

theorem partialTranspose_kronecker (X : Operator a) (Y : Operator b) :
    partialTranspose (X ⊗ₖ Y) = X ⊗ₖ Y.transpose := rfl

theorem replacer_isPPT (d : ℕ) (ω : State b) : IsPPT (ReplacerChannel.channel d ω).toLinearMap := by
  rw [IsPPT,MatrixMap.choi_toLinearMap,ReplacerChannel.channel_choi,partialTranspose_kronecker]
  exact MatrixMap.posSemidef_kronecker Matrix.PosSemidef.one ω.positive.transpose

theorem reindex_isPPT {a' b' : ℕ} (ea : Fin a ≃ Fin a') (eb : Fin b ≃ Fin b')
    (Φ : KrausChannel a b) (hΦ : IsPPT Φ.toLinearMap) :
    IsPPT (reindexChannel ea eb Φ).toLinearMap := by
  have h : partialTranspose (reindexChannel ea eb Φ).choi =
      Matrix.reindex (Equiv.prodCongr ea eb) (Equiv.prodCongr ea eb) (partialTranspose Φ.choi) := by
    rw [reindexChannel_choi]
    rfl
  change (partialTranspose (reindexChannel ea eb Φ).choi).PosSemidef
  rw [h]
  exact hΦ.submatrix _

theorem tensor_isPPT {c d : ℕ} (Φ : KrausChannel a b) (Ψ : KrausChannel c d)
    (hΦ : IsPPT Φ.toLinearMap) (hΨ : IsPPT Ψ.toLinearMap) : IsPPT (Φ.tensor Ψ).toLinearMap := by
  have h : partialTranspose (Φ.tensor Ψ).choi =
      Matrix.reindex (MatrixMap.choiShuffle a b c d) (MatrixMap.choiShuffle a b c d)
        (partialTranspose Φ.choi ⊗ₖ partialTranspose Ψ.choi) := by
    rw [← MatrixMap.choi_toLinearMap,← MatrixMap.tensor_kraus_toLinearMap,MatrixMap.choi_tensor]
    ext ⟨i,x⟩ ⟨j,y⟩
    rfl
  change (partialTranspose (Φ.tensor Ψ).choi).PosSemidef
  rw [h]
  exact (MatrixMap.posSemidef_kronecker hΦ hΨ).submatrix _

/-- Partial trace commutes with transposition of the entire discarded/output system. -/
theorem discardRight_transpose (d e : ℕ) (X : Operator (d*e)) :
    (discardRight d e).apply X.transpose = ((discardRight d e).apply X).transpose := by
  obtain ⟨Y,rfl⟩ := (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv).surjective X
  change (discardRight d e).apply (Matrix.reindex finProdFinEquiv finProdFinEquiv Y).transpose =
    ((discardRight d e).apply (Matrix.reindex finProdFinEquiv finProdFinEquiv Y)).transpose
  rw [Matrix.transpose_reindex,discardRight_apply,discardRight_apply]
  rfl

/-- Arbitrary input processing and the actual output discard preserve PPT. -/
theorem marginal_isPPT (n : ℕ) (τ : State a) (Φ : KrausChannel (a^(n+1)) (b^(n+1)))
    (hΦ : IsPPT Φ.toLinearMap) : IsPPT (marginalChannel n τ Φ).toLinearMap := by
  let Ψ := reindexChannel (channelAddEquiv a n 1).symm (channelAddEquiv b n 1).symm Φ
  have hp : IsPPT Ψ.toLinearMap := reindex_isPPT _ _ Φ hΦ
  have hcp := (isPPT_iff_transpose_comp_cp Ψ.toLinearMap).mp hp
  have h := completelyPositive_comp
    (completelyPositive_comp (MatrixMap.completelyPositive_toLinearMap (appendState (a^n) (statePower τ 1))) hcp)
    (MatrixMap.completelyPositive_toLinearMap (discardRight (b^n) (b^1)))
  apply (isPPT_iff_transpose_comp_cp _).mpr
  have he : (transposeMap (b^n)).comp (marginalChannel n τ Φ).toLinearMap =
      (discardRight (b^n) (b^1)).toLinearMap.comp
        (((transposeMap (b^n*b^1)).comp Ψ.toLinearMap).comp (appendState (a^n) (statePower τ 1)).toLinearMap) := by
    ext X i j
    change ((marginalChannel n τ Φ).apply X).transpose i j =
      (discardRight (b^n) (b^1)).apply ((Ψ.apply ((appendState _ _).apply X)).transpose) i j
    simp only [marginalChannel,KrausChannel.compose_apply,discardRight_transpose]
    rfl
  rw [he]
  exact h

theorem ppt_admissible (ω : State b) (hω : ω.matrix.PosDef) : Admissible (PPTFamily a b) where
  channels n hn Φ hΦ := hΦ.1
  nonempty n hn := ⟨(ReplacerChannel.channel (a^n) (statePower ω n)).toLinearMap,
    ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,replacer_isPPT _ _⟩⟩
  compact n hn := by
    rw [ppt_choi_image]
    exact (isCompact_channelChoiSet _ _).inter_right (isClosed_pptChoi _ _)
  convex n hn := by
    rw [ppt_choi_image]
    exact (convex_channelChoiSet _ _).inter (convex_pptChoi _ _)
  tensor_closed n m hn hm Φ Ψ hΦ hΨ :=
    ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩, reindex_isPPT _ _ _ (tensor_isPPT Φ Ψ hΦ.2 hΨ.2)⟩
  faithful_replacer := by
    refine ⟨ω,hω,⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩⟩
    rw [ReplacerChannel.tensorPower_map,← ReplacerChannel.channel_map]
    exact replacer_isPPT _ _

theorem ppt_quantitative (τ : State a) (hτ : τ.matrix.PosDef) : QuantitativeAt (PPTFamily a b) τ where
  faithful := hτ
  permutation_closed n hn π Φ hΦ :=
    ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,reindex_isPPT _ _ Φ hΦ.2⟩
  marginal_closed n hn Φ hΦ :=
    ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,marginal_isPPT n τ Φ hΦ.2⟩

end GeneralizedChannelStein
