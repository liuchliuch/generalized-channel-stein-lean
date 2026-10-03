import GeneralizedChannelStein.LocalChoiDomination
import GeneralizedChannelStein.BulkMarginal
import GeneralizedChannelStein.SiteGrouping
import GeneralizedChannelStein.WeightedGramMixture
import GeneralizedChannelStein.TensorStateLowerBound

/-! # Exact local multiplier costs and actual site replacement channels -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.FreeMultipliers
open QuantumChannelStein Matrix ChannelEntropy ChannelPowerReindex PerfectDiscrimination
  BranchExtraction LocalExpansion LocalReplacement LocalChoiDomination ChannelTransport SiteGrouping
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a d n : ℕ}

/-- Equivalent positive square-root form of the paper's h_r. -/
def localCost (a d : ℕ) (t w : ℝ) (r : ℕ) : ℝ := Real.sqrt (((a*d:ℕ):ℝ)/(t*w))^r

theorem localCost_pos (ha : 0<a) (hd : 0<d) {t w : ℝ} (ht : 0<t) (hw : 0<w) (r : ℕ) :
    0<localCost a d t w r := by unfold localCost; positivity

theorem localCost_sq (t w : ℝ) (ht : 0<t) (hw : 0<w) (r : ℕ) :
    (localCost a d t w r)^2=(((a*d:ℕ):ℝ)/(t*w))^r := by
  rw [localCost,← pow_mul, mul_comm r 2,pow_mul,Real.sq_sqrt (by positivity)]

theorem localCost_coefficient (ha : 0<a) (hd : 0<d) (t w p : ℝ) (ht : 0<t) (hw : 0<w) (r : ℕ) :
    p/(localCost a d t w r)^2=p*t^r*w^r/((a^r*d^r:ℕ):ℝ) := by
  rw [localCost_sq t w ht hw,div_pow,mul_pow]
  push_cast
  field_simp
  ring

/-- The literal simultaneous input/output site replacement channel. -/
def replaceSites (M : KrausChannel (a^n) (d^n)) (τ : State a) (ω : State d) (S : Finset (Fin n)) :
    KrausChannel (a^n) (d^n) :=
  reindexChannel (groupIndex a S).symm (groupIndex d S).symm
    (replacedChannel (reindexChannel (groupIndex a S) (groupIndex d S) M)
      (statePower τ S.card) (statePower ω S.card))

theorem reindexMap_adMap {a b a' b' : ℕ} (ea : Fin a≃Fin a') (eb : Fin b≃Fin b')
    (K : Matrix (Fin b) (Fin a) ℂ) :
    reindexMap ea eb (adMap K)=adMap (Matrix.reindex eb ea K) := by
  apply MatrixMap.choi_injective
  ext ⟨i,u⟩ ⟨j,v⟩
  change reindexMap ea eb (adMap K) (Matrix.single i j 1) u v =
    adMap (Matrix.reindex eb ea K) (Matrix.single i j 1) u v
  rw [reindexMap_apply,reindex_single]
  change MatrixMap.choi (adMap K) (ea.symm i,eb.symm u) (ea.symm j,eb.symm v)=
    MatrixMap.choi (adMap (Matrix.reindex eb ea K)) (i,u) (j,v)
  rw [choi_adMap_apply,choi_adMap_apply]
  rfl

/-- Grouped local contraction and grouped branch have the same physical product. -/
theorem grouped_product (S : Finset (Fin n)) (F : Block (Fin d) n)
    (K : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) :
    Matrix.reindex (groupIndex d S) (groupIndex a S) (SiteGrouping.flatten F*K)=
      Matrix.reindex (groupIndex d S) (groupIndex d S) (SiteGrouping.flatten F) *
        Matrix.reindex (groupIndex d S) (groupIndex a S) K :=
  (Matrix.reindexLinearEquiv_mul ℂ ℂ (groupIndex d S) (groupIndex d S) (groupIndex a S) _ _).symm

/-- The single-support CP comparison, with actual replacements on precisely
that chosen set of sites. Its freeness is proved separately from F1--F5. -/
theorem single_support_cpLe (M : KrausChannel (a^n) (d^n))
    (τ : State a) (ω : State d) (ha : 0<a) (hd : 0<d)
    (t w p : ℝ) (ht : 0<t) (hw : 0<w) (hp : 0<p)
    (htτ : (τ.matrix-t•(1:Operator a)).PosSemidef)
    (hwω : (ω.matrix-w•(1:Operator d)).PosSemidef)
    (K : Matrix (Fin (d^n)) (Fin (a^n)) ℂ)
    (hdom : MatrixMap.CPLe (Complex.ofReal p • adMap K) M.toLinearMap)
    (S : Finset (Fin n)) (F : Block (Fin d) n) (hsupp : SupportedOn S F) (hF : ‖F‖≤1) :
    MatrixMap.CPLe (Complex.ofReal (p/(localCost a d t w S.card)^2) • adMap (SiteGrouping.flatten F*K))
      (replaceSites M τ ω S).toLinearMap := by
  obtain ⟨G,hG,hGid⟩ := exists_local_contraction S F hsupp hF hd
  let ea := groupIndex a S
  let ed := groupIndex d S
  let M' := reindexChannel ea ed M
  let K' := Matrix.reindex ed ea K
  have hdom' : MatrixMap.CPLe (Complex.ofReal p • adMap K') M'.toLinearMap := by
    have h := reindexMap_cpLe ea ed _ _ hdom
    simpa only [reindexMap_smul,reindexMap_adMap,← reindexChannel_map] using h
  have hlocal := local_multiplier_cpLe M'.toLinearMap K' G hG (statePower τ S.card).matrix
    (statePower ω S.card).matrix (statePower τ S.card).positive (statePower ω S.card).positive
    (t^S.card) (w^S.card) p (pow_pos ht _) (pow_pos hw _) hp.le (pow_pos ha _) (pow_pos hd _)
    (TensorStateLowerBound.statePower_lower τ t ht.le htτ S.card)
    (TensorStateLowerBound.statePower_lower ω w hw.le hwω S.card) hdom'
  rw [← replacedChannel_map] at hlocal
  have hback := reindexMap_cpLe ea.symm ed.symm _ _ hlocal
  rw [reindexMap_smul,reindexMap_adMap,← reindexChannel_map] at hback
  have hprod : outputLocal (d^(n-S.card)) G*K'=Matrix.reindex ed ea (SiteGrouping.flatten F*K) := by
    rw [grouped_product,hGid]
    rfl
  rw [hprod] at hback
  have hcancel : Matrix.reindex ed.symm ea.symm (Matrix.reindex ed ea (SiteGrouping.flatten F*K))=
      SiteGrouping.flatten F*K := by
    ext i j
    change (SiteGrouping.flatten F*K) (ed.symm (ed i)) (ea.symm (ea j))=(SiteGrouping.flatten F*K) i j
    simp only [Equiv.symm_apply_apply]
  rw [hcancel] at hback
  rw [localCost_coefficient ha hd t w p ht hw]
  exact hback

theorem scalar_channel_map (P : KrausChannel 1 1) : P.toLinearMap=(KrausChannel.identity 1).toLinearMap := by
  ext X i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i
  subst j
  have h := P.trace_apply X
  change P.apply X 0 0=(KrausChannel.identity 1).apply X 0 0
  rw [KrausChannel.identity_apply]
  simpa only [Matrix.trace,Matrix.diag,Fin.sum_univ_one] using h

/-- The full-support case uses the normalized one-dimensional marginal,
so no membership condition at block zero is needed. -/
theorem bulk_replacement_mem (F : AlternativeFamily a d) (hF : Admissible F)
    (τ : State a) (hτ : QuantitativeAt F τ) (ω : State d)
    (hω : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (k r : ℕ) (hr : 0<r) (P : KrausChannel (a^(k+r)) (d^(k+r))) (hP : P.toLinearMap∈F (k+r)) :
    (tensorBlocks k r (iteratedMarginal k τ r P) (ReplacerChannel.channel (a^r) (statePower ω r))).toLinearMap∈F (k+r) := by
  by_cases hk : 0<k
  · rw [BulkMarginal.tensor_iterated_eq_replaced]
    exact BulkMarginal.replacedMap_mem F hF τ hτ ω hω k r hk hr P hP
  · have hk0 : k=0 := by omega
    subst k
    have hzero : (iteratedMarginal 0 τ r P).toLinearMap=
        ((ReplacerChannel.channel a ω).tensorPower 0).toLinearMap :=
      scalar_channel_map _
    have hR : (ReplacerChannel.channel (a^r) (statePower ω r)).toLinearMap=
        ((ReplacerChannel.channel a ω).tensorPower r).toLinearMap := by
      rw [ReplacerChannel.channel_map,ReplacerChannel.tensorPower_map]
    rw [RepeatedBlocks.tensorBlocks_map_congr 0 r _ _ _ _ hzero hR]
    rw [show (tensorBlocks 0 r ((ReplacerChannel.channel a ω).tensorPower 0)
      ((ReplacerChannel.channel a ω).tensorPower r)).toLinearMap=
      ((ReplacerChannel.channel a ω).tensorPower (0+r)).toLinearMap from tensorPower_add_toLinearMap _ _ _]
    exact replacer_power_mem F hF.tensor_closed ω hω (0+r) (by omega)

/-- F4 groups the chosen sites, F5 removes them, F2 restores the replacer,
and inverse F4 returns to the original sites. No arbitrary-processing closure is used. -/
theorem replaceSites_mem_nonempty (F : AlternativeFamily a d) (hF : Admissible F)
    (τ : State a) (hτ : QuantitativeAt F τ) (ω : State d)
    (hω : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (hn : 0<n) (M : KrausChannel (a^n) (d^n)) (hM : M.toLinearMap∈F n)
    (S : Finset (Fin n)) (hr : 0<S.card) :
    (replaceSites M τ ω S).toLinearMap∈F n := by
  let k := n-S.card
  let r := S.card
  let hkr : k+r=n := keep_add_card S
  let π := permutation S
  let P := permuteChannel n π M
  have hP : P.toLinearMap∈F n := hτ.permutation_closed n hn π M hM
  let P' := P.cast (congrArg (a^·) hkr.symm) (congrArg (d^·) hkr.symm)
  have hP' : P'.toLinearMap∈F (k+r) := (RepeatedBlocks.cast_mem_family F hkr.symm P).mpr hP
  let Q := tensorBlocks k r (iteratedMarginal k τ r P') (ReplacerChannel.channel (a^r) (statePower ω r))
  have hQ : Q.toLinearMap∈F (k+r) := by
    exact bulk_replacement_mem F hF τ hτ ω hω k r hr P' hP'
  let Q' := Q.cast (congrArg (a^·) hkr) (congrArg (d^·) hkr)
  have hQ' : Q'.toLinearMap∈F n := (RepeatedBlocks.cast_mem_family F hkr Q).mpr hQ
  have hback := hτ.permutation_closed n hn π.symm Q' hQ'
  have heq : (permuteChannel n π.symm Q').toLinearMap=(replaceSites M τ ω S).toLinearMap := by
    have hQmap := BulkMarginal.tensor_iterated_eq_replaced k r τ ω P'
    have hcast {u v u' v' : ℕ} (C : KrausChannel u v) (hu : u=u') (hv : v=v') :
        (C.cast hu hv).toLinearMap=reindexMap (finCongr hu) (finCongr hv) C.toLinearMap := by
      rw [← RepeatedBlocks.reindexChannel_finCongr,reindexChannel_map]
    simp only [permuteChannel,reindexChannel_map,Q',hcast]
    change reindexMap (sitePermutation a n π.symm) (sitePermutation d n π.symm)
      (reindexMap (finCongr (congrArg (a^·) hkr)) (finCongr (congrArg (d^·) hkr)) Q.toLinearMap)=_
    rw [hQmap]
    simp only [P',hcast,P,permuteChannel,reindexChannel_map,reindexMap_trans]
    simp only [replaceSites,reindexChannel_map,replacedChannel_map,reindexChannel_map]
    rw [groupIndex_eq_permutation_add,groupIndex_eq_permutation_add]
    simp only [sitePermutation_symm]
    congr 1
  rwa [heq] at hback

theorem statePower_zero_matrix {b : ℕ} (ρ : State b) : (statePower ρ 0).matrix=(1:Operator 1) := by
  letI : Subsingleton (Fin (b^0)) := by rw [pow_zero]; infer_instance
  ext i j
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [statePower,TensorPower.tensorPower,Matrix.reindex_apply,Matrix.one_apply]

theorem replaceSites_empty_map (M : KrausChannel (a^n) (d^n)) (τ : State a) (ω : State d) :
    (replaceSites M τ ω ∅).toLinearMap=M.toLinearMap := by
  rw [replaceSites,reindexChannel_map,replacedChannel_map]
  simp only [Finset.card_empty,Nat.sub_zero,pow_zero,statePower_zero_matrix]
  rw [replacedMap_scalar,reindexChannel_map,reindexMap_inverse]

/-- Actual replacement is free for every support, including empty and full support. -/
theorem replaceSites_mem (F : AlternativeFamily a d) (hF : Admissible F)
    (τ : State a) (hτ : QuantitativeAt F τ) (ω : State d)
    (hω : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (hn : 0<n) (M : KrausChannel (a^n) (d^n)) (hM : M.toLinearMap∈F n) (S : Finset (Fin n)) :
    (replaceSites M τ ω S).toLinearMap∈F n := by
  by_cases hS : S=∅
  · subst S
    rwa [replaceSites_empty_map]
  · exact replaceSites_mem_nonempty F hF τ hτ ω hω hn M hM S (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS))

/-- Literal paper h_r, including its negative real exponent. -/
def paperCost (a d : ℕ) (t w : ℝ) (r : ℕ) : ℝ :=
  ((a*d:ℕ):ℝ)^r * (((a:ℝ)*t)*((d:ℝ)*w))^(-(r:ℝ)/2)

theorem localCost_eq_paperCost (ha : 0<a) (hd : 0<d) (t w : ℝ) (ht : 0<t) (hw : 0<w) (r : ℕ) :
    localCost a d t w r=paperCost a d t w r := by
  have ha' : (0:ℝ)<a := by exact_mod_cast ha
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hp : 0<paperCost a d t w r := by unfold paperCost; positivity
  apply (sq_eq_sq₀ (localCost_pos ha hd ht hw r).le hp.le).mp
  rw [localCost_sq t w ht hw,paperCost,mul_pow,← Real.rpow_mul_natCast (by positivity)]
  rw [show (-(r:ℝ)/2)*(2:ℕ)=-(r:ℝ) by push_cast; ring,
    Real.rpow_neg (by positivity),Real.rpow_natCast]
  push_cast
  rw [div_pow,mul_pow,mul_pow,mul_pow]
  field_simp
  ring

/-- The finite expansion version with any proved faithful eigenvalue lower bounds. -/
theorem multiplier_of_expansion (F : AlternativeFamily a d) (hF : Admissible F)
    (τ : State a) (hτ : QuantitativeAt F τ) (ω : State d)
    (hω : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (ha : 0<a) (hd : 0<d) (hn : 0<n) (t w p : ℝ) (ht : 0<t) (hw : 0<w) (hp : 0<p)
    (htτ : (τ.matrix-t•(1:Operator a)).PosSemidef) (hwω : (ω.matrix-w•(1:Operator d)).PosSemidef)
    (M : KrausChannel (a^n) (d^n)) (hM : M.toLinearMap∈F n)
    (K : Matrix (Fin (d^n)) (Fin (a^n)) ℂ)
    (hdom : MatrixMap.CPLe (Complex.ofReal p • adMap K) M.toLinearMap)
    (E : LocalExpansion.Expansion (Fin d) n)
    (hH : 0<∑ i : E.terms, ‖E.coeff i‖*paperCost a d t w (E.sites i).card) :
    ∃ M' : KrausChannel (a^n) (d^n), M'.toLinearMap∈F n ∧
      MatrixMap.CPLe
        (Complex.ofReal (p/(∑ i : E.terms, ‖E.coeff i‖*paperCost a d t w (E.sites i).card)^2) •
          adMap (SiteGrouping.flatten E.value*K)) M'.toLinearMap := by
  let h : E.terms→ℝ := fun i => paperCost a d t w (E.sites i).card
  let Ki : E.terms→Matrix (Fin (d^n)) (Fin (a^n)) ℂ := fun i => SiteGrouping.flatten (E.factor i)*K
  let Mi : E.terms→KrausChannel (a^n) (d^n) := fun i => replaceSites M τ ω (E.sites i)
  have hhi (i : E.terms) : 0<h i := by
    dsimp only [h]
    rw [← localCost_eq_paperCost ha hd t w ht hw]
    exact localCost_pos ha hd ht hw _
  have hMi (i : E.terms) : (Mi i).toLinearMap∈F n := replaceSites_mem F hF τ hτ ω hω hn M hM (E.sites i)
  have hdi (i : E.terms) : MatrixMap.CPLe (Complex.ofReal (p/(h i)^2) • adMap (Ki i)) (Mi i).toLinearMap := by
    have hh := single_support_cpLe M τ ω ha hd t w p ht hw hp htτ hwω K hdom
      (E.sites i) (E.factor i) (E.supported i) (E.contraction i)
    simpa only [localCost_eq_paperCost ha hd t w ht hw] using hh
  obtain ⟨M',hM',horder⟩ := WeightedGramMixture.free_mixture_dominator (F n) (hF.convex n hn)
    E.coeff h Ki Mi hp hhi hH hMi hdi
  refine ⟨M',hM',?_⟩
  have heq : (∑ i : E.terms, E.coeff i • Ki i)=SiteGrouping.flatten E.value*K := by
    ext x y
    simp [Ki,SiteGrouping.flatten,LocalExpansion.Expansion.value,Matrix.reindex_apply,
      Matrix.mul_apply,Matrix.sum_apply,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
  rw [heq] at horder
  exact horder

/-- Lemma28: literal minimum eigenvalues, literal h_r and H, actual free CP
dominator, arbitrary complex coefficients and arbitrary chosen finite supports. -/
theorem lemma_28 (F : AlternativeFamily a d) (hF : Admissible F)
    (τ : State a) (hτ : QuantitativeAt F τ) (ω : State d) (hωpos : ω.matrix.PosDef)
    (hω : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (ha : 0<a) (hd : 0<d) (hn : 0<n)
    (M : KrausChannel (a^n) (d^n)) (hM : M.toLinearMap∈F n)
    (K : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) (p : ℝ) (hp : 0<p)
    (hdom : MatrixMap.CPLe (Complex.ofReal p • adMap K) M.toLinearMap)
    (E : LocalExpansion.Expansion (Fin d) n)
    (hH : 0<∑ i : E.terms, ‖E.coeff i‖*paperCost a d
      (DimensionDomination.minEigenvalue τ ha) (DimensionDomination.minEigenvalue ω hd) (E.sites i).card) :
    ∃ M' : KrausChannel (a^n) (d^n), M'.toLinearMap∈F n ∧
      MatrixMap.CPLe
        (Complex.ofReal (p/(∑ i : E.terms, ‖E.coeff i‖*paperCost a d
          (DimensionDomination.minEigenvalue τ ha) (DimensionDomination.minEigenvalue ω hd) (E.sites i).card)^2) •
          adMap (SiteGrouping.flatten E.value*K)) M'.toLinearMap :=
  multiplier_of_expansion F hF τ hτ ω hω ha hd hn _ _ p
    (DimensionDomination.minEigenvalue_pos τ ha hτ.faithful)
    (DimensionDomination.minEigenvalue_pos ω hd hωpos) hp
    (DimensionDomination.scalar_le_of_eigenvalue_lower τ _ (DimensionDomination.minEigenvalue_le τ ha))
    (DimensionDomination.scalar_le_of_eigenvalue_lower ω _ (DimensionDomination.minEigenvalue_le ω hd))
    M hM K hdom E hH

end GeneralizedChannelStein.FreeMultipliers
