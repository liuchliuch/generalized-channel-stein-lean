import GeneralizedChannelStein.IsometryLift
import GeneralizedChannelStein.CovariantFamilies
import GeneralizedChannelStein.SiteGrouping

/-! Exact tensor and coordinate transport for actual Heisenberg channels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.HeisenbergTensor
open QuantumChannelStein Matrix ChannelEntropy ChannelPowerReindex ChannelTransport
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b c d a' b' : ℕ}

theorem tensor_product (Φ : KrausChannel a b) (Ψ : KrausChannel c d)
    (X : Operator b) (Y : Operator d) :
    heisenbergMap (Φ.tensor Ψ) (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y)) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (heisenbergMap Φ X ⊗ₖ heisenbergMap Ψ Y) := by
  rw [heisenbergMap_apply]
  change (∑ k : Fin (Φ.rank*Ψ.rank),
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (KrausChannel.tensorKraus Φ Ψ (finProdFinEquiv.symm k)))ᴴ *
      Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y) *
      Matrix.reindex finProdFinEquiv finProdFinEquiv (KrausChannel.tensorKraus Φ Ψ (finProdFinEquiv.symm k))) = _
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply,Matrix.conjTranspose_reindex]
  change (∑ k : Fin Φ.rank × Fin Ψ.rank,
    Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (KrausChannel.tensorKraus Φ Ψ k)ᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y) *
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (KrausChannel.tensorKraus Φ Ψ k)) = _
  simp_rw [Matrix.reindexLinearEquiv_mul]
  rw [← map_sum]
  apply congrArg (fun M : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ =>
    Matrix.reindex finProdFinEquiv finProdFinEquiv M)
  simp only [KrausChannel.tensorKraus,Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,
    Fintype.sum_prod_type,heisenbergMap_apply]
  change (∑ k : Fin Φ.rank × Fin Ψ.rank, ((Φ.kraus k.1)ᴴ*X*Φ.kraus k.1) ⊗ₖ ((Ψ.kraus k.2)ᴴ*Y*Ψ.kraus k.2)) = _
  rw [Fintype.sum_prod_type]
  exact (sum_kronecker_sum (fun i : Fin Φ.rank => (Φ.kraus i)ᴴ*X*Φ.kraus i)
    (fun j : Fin Ψ.rank => (Ψ.kraus j)ᴴ*Y*Ψ.kraus j)).symm

theorem reindex_apply (Φ : KrausChannel a b) (ea : Fin a≃Fin a') (eb : Fin b≃Fin b')
    (X : Operator b) :
    heisenbergMap (reindexChannel ea eb Φ) (Matrix.reindex eb eb X) =
      Matrix.reindex ea ea (heisenbergMap Φ X) := by
  simp only [heisenbergMap_apply,reindexChannel,Matrix.conjTranspose_reindex]
  change (∑ k, Matrix.reindexLinearEquiv ℂ ℂ ea eb (Φ.kraus k)ᴴ *
    Matrix.reindexLinearEquiv ℂ ℂ eb eb X * Matrix.reindexLinearEquiv ℂ ℂ eb ea (Φ.kraus k)) = _
  simp_rw [Matrix.reindexLinearEquiv_mul]
  exact (map_sum (Matrix.reindexLinearEquiv ℂ ℂ ea ea) _ _).symm

theorem congr_channel (Φ Ψ : KrausChannel a b) (h : Φ.toLinearMap=Ψ.toLinearMap) :
    heisenbergMap Φ=heisenbergMap Ψ := by
  ext X i j
  have hM : heisenbergMap Φ X=heisenbergMap Ψ X := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro Y
    rw [heisenbergMap_pairing,heisenbergMap_pairing]
    have he := congrArg (fun f : MatrixMap a b => f Y) h
    exact congrArg (fun Z => (Z*X).trace) he
  exact congrFun (congrFun hM i) j

theorem cast_apply (Φ : KrausChannel a b) (ha : a=a') (hb : b=b') (X : Operator b) :
    heisenbergMap (Φ.cast ha hb) (Matrix.reindex (finCongr hb) (finCongr hb) X) =
      Matrix.reindex (finCongr ha) (finCongr ha) (heisenbergMap Φ X) := by
  subst a'; subst b'; rfl

/-- Simultaneous site permutation commutes with the full Heisenberg action. -/
theorem permutation_apply (Φ : KrausChannel a b) (n : ℕ) (π : Equiv.Perm (Fin n))
    (X : Operator (b^n)) :
    heisenbergMap (Φ.tensorPower n) (Matrix.reindex (sitePermutation b n π) (sitePermutation b n π) X) =
      Matrix.reindex (sitePermutation a n π) (sitePermutation a n π) (heisenbergMap (Φ.tensorPower n) X) := by
  have h := reindex_apply (Φ.tensorPower n) (sitePermutation a n π) (sitePermutation b n π) X
  have he := congr_channel (permuteChannel n π (Φ.tensorPower n)) (Φ.tensorPower n)
    (permute_power_map Φ n π)
  change heisenbergMap (permuteChannel n π (Φ.tensorPower n)) _ = _ at h
  rw [he] at h
  exact h


theorem split_apply (Φ : KrausChannel a b) (k r : ℕ) (X : Operator (b^k*b^r)) :
    heisenbergMap (Φ.tensorPower (k+r)) (Matrix.reindex (channelAddEquiv b k r) (channelAddEquiv b k r) X) =
      Matrix.reindex (channelAddEquiv a k r) (channelAddEquiv a k r)
        (heisenbergMap ((Φ.tensorPower k).tensor (Φ.tensorPower r)) X) := by
  have h := reindex_apply ((Φ.tensorPower k).tensor (Φ.tensorPower r))
    (channelAddEquiv a k r) (channelAddEquiv b k r) X
  rw [congr_channel _ _ (tensorPower_add_toLinearMap Φ k r)] at h
  exact h

theorem split_inverse_apply (Φ : KrausChannel a b) (k r : ℕ) (X : Operator (b^(k+r))) :
    Matrix.reindex (channelAddEquiv a k r).symm (channelAddEquiv a k r).symm
      (heisenbergMap (Φ.tensorPower (k+r)) X) =
    heisenbergMap ((Φ.tensorPower k).tensor (Φ.tensorPower r))
      (Matrix.reindex (channelAddEquiv b k r).symm (channelAddEquiv b k r).symm X) := by
  have h := split_apply Φ k r (Matrix.reindex (channelAddEquiv b k r).symm (channelAddEquiv b k r).symm X)
  have he := congrArg (fun Y => Matrix.reindex (channelAddEquiv a k r).symm (channelAddEquiv a k r).symm Y) h
  simpa [Matrix.reindex_apply,Matrix.submatrix_submatrix] using he

/-- Arbitrary chosen-site grouping, with no processing-closure premise. -/
theorem group_apply (Φ : KrausChannel a b) (n : ℕ) (S : Finset (Fin n)) (X : Operator (b^n)) :
    Matrix.reindex (SiteGrouping.groupIndex a S) (SiteGrouping.groupIndex a S)
      (heisenbergMap (Φ.tensorPower n) X) =
    heisenbergMap ((Φ.tensorPower (n-S.card)).tensor (Φ.tensorPower S.card))
      (Matrix.reindex (SiteGrouping.groupIndex b S) (SiteGrouping.groupIndex b S) X) := by
  have generic (n k r : ℕ) (hn : n=k+r) (π : Equiv.Perm (Fin n)) (X : Operator (b^n)) :
      Matrix.reindex (((sitePermutation a n π).trans (finCongr (congrArg (a^·) hn))).trans (channelAddEquiv a k r).symm)
        (((sitePermutation a n π).trans (finCongr (congrArg (a^·) hn))).trans (channelAddEquiv a k r).symm)
        (heisenbergMap (Φ.tensorPower n) X) =
      heisenbergMap ((Φ.tensorPower k).tensor (Φ.tensorPower r))
        (Matrix.reindex (((sitePermutation b n π).trans (finCongr (congrArg (b^·) hn))).trans (channelAddEquiv b k r).symm)
          (((sitePermutation b n π).trans (finCongr (congrArg (b^·) hn))).trans (channelAddEquiv b k r).symm) X) := by
    subst n
    have h := split_inverse_apply Φ k r (Matrix.reindex (sitePermutation b (k+r) π) (sitePermutation b (k+r) π) X)
    rw [permutation_apply] at h
    simpa [Matrix.reindex_apply,Matrix.submatrix_submatrix] using h
  simpa only [SiteGrouping.groupIndex_eq_permutation_add] using
    generic n (n-S.card) S.card (SiteGrouping.keep_add_card S).symm (SiteGrouping.permutation S) X

end GeneralizedChannelStein.HeisenbergTensor
