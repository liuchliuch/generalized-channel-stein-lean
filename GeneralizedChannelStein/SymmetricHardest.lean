import GeneralizedChannelStein.OperationalMinimax
import GeneralizedChannelStein.WeightedGramMixture
import GeneralizedChannelStein.QuantitativeFamilies
import QuantumChannelStein.CanonicalCovariantOutput

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.SymmetricHardest
open QuantumChannelStein ChannelEntropy ChannelPowerReindex PerfectDiscrimination
  CovariantOrbitRecovery CovariantOrbitInput TestingSDP TestingPrimal
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

theorem singleBeta_congr (N N' M M' : KrausChannel a b) (ε : ℝ)
    (hN : N.toLinearMap = N'.toLinearMap) (hM : M.toLinearMap = M'.toLinearMap) :
    singleBeta N M ε = singleBeta N' M' ε := by
  unfold singleBeta
  apply le_antisymm
  · apply le_iInf
    intro x
    have hp : 1-ε ≤ x.val.2.probability (pureOutput N x.val.1) := by
      rw [pureOutput_congr N N' hN]
      exact x.property
    refine iInf_le_of_le ⟨x.val,hp⟩ ?_
    rw [pureOutput_congr M M' hM]
  · apply le_iInf
    intro x
    have hp : 1-ε ≤ x.val.2.probability (pureOutput N' x.val.1) := by
      rw [← pureOutput_congr N N' hN]
      exact x.property
    refine iInf_le_of_le ⟨x.val,hp⟩ ?_
    rw [← pureOutput_congr M M' hM]

theorem singleBeta_reindex_le (p : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b))
    (N M : KrausChannel a b) (ε : ℝ) :
    singleBeta (reindexChannel p q N) (reindexChannel p q M) ε ≤ singleBeta N M ε := by
  unfold singleBeta
  apply le_iInf
  intro x
  let ψ := reindexInput p x.val.1
  let T := reindexEffect (outputReindex p q) x.val.2
  have hp : 1-ε ≤ T.probability (pureOutput (reindexChannel p q N) ψ) := by
    dsimp [ψ,T]
    rw [pureOutput_reindexChannel,reindexEffect_probability]
    exact x.property
  refine iInf_le_of_le ⟨(ψ,T),hp⟩ ?_
  dsimp only [ψ,T]
  rw [pureOutput_reindexChannel,reindexEffect_probability]

theorem reindexChannel_inverse_map (p : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b))
    (M : KrausChannel a b) :
    (reindexChannel p.symm q.symm (reindexChannel p q M)).toLinearMap = M.toLinearMap := by
  apply MatrixMap.choi_injective
  simp only [MatrixMap.choi_toLinearMap, reindexChannel_choi]
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [Matrix.reindex_apply]

theorem singleBeta_reindex (p : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b))
    (N M : KrausChannel a b) (ε : ℝ) :
    singleBeta (reindexChannel p q N) (reindexChannel p q M) ε = singleBeta N M ε := by
  apply le_antisymm (singleBeta_reindex_le p q N M ε)
  have h := singleBeta_reindex_le p.symm q.symm (reindexChannel p q N) (reindexChannel p q M) ε
  rwa [singleBeta_congr _ N _ M ε (reindexChannel_inverse_map p q N) (reindexChannel_inverse_map p q M)] at h

/-- Finite concavity in the alternative channel, proved from actual tester values. -/
theorem singleBeta_mixture_lower {ι : Type*} [Fintype ι]
    (N A : KrausChannel a b) (M : ι → KrausChannel a b) (ε : ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hA : A.toLinearMap = ∑ i, (w i:ℂ) • (M i).toLinearMap)
    (β : ENNReal) (hβ : β ≠ ⊤) (hβM : ∀ i, β ≤ singleBeta N (M i) ε) :
    β ≤ singleBeta N A ε := by
  rw [singleBeta_eq_primal]
  apply le_iInf
  intro x
  have hval (i : ι) : β.toReal ≤ testerValue x.val (M i).choi := by
    have hle : β ≤ ENNReal.ofReal (testerValue x.val (M i).choi) := (hβM i).trans (by
      rw [singleBeta_eq_primal]
      exact iInf_le (fun y : testerSet N ε => ENNReal.ofReal (testerValue y.val (M i).choi)) x)
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (testerValue_bounds x.val x.property.1 (M i)).1] at ht
  have hav : testerValue x.val A.choi = ∑ i, w i*testerValue x.val (M i).choi := by
    rw [← MatrixMap.choi_toLinearMap, hA, WeightedGramMixture.choi_real_sum]
    simp [testerValue, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul]
  have hsumval := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hval i) (hw i))
  have hreal : β.toReal ≤ testerValue x.val A.choi := by
    rw [hav]
    simpa [← Finset.sum_mul, hsum] using hsumval
  rw [← ENNReal.ofReal_toReal hβ]
  exact ENNReal.ofReal_le_ofReal hreal


variable {G : Type*} [Fintype G] [Group G] [DecidableEq G]

omit [DecidableEq G] in
theorem sum_weight : (∑ _g : G, weight G) = 1 := by
  have hc : (Fintype.card G:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [weight, hc]

def orbitMap (p : G →* Equiv.Perm (Fin a)) (q : G →* Equiv.Perm (Fin b))
    (M : KrausChannel a b) : MatrixMap a b :=
  ∑ g, (weight G:ℂ) • (reindexChannel (p g) (q g) M).toLinearMap

theorem orbitMap_isChannel (p : G →* Equiv.Perm (Fin a)) (q : G →* Equiv.Perm (Fin b))
    (M : KrausChannel a b) : IsChannel (orbitMap p q M) :=
  WeightedGramMixture.finite_mixture_isChannel _ (fun _ => weight G)
    (fun _ => weight_pos.le) sum_weight

def orbitChannel (p : G →* Equiv.Perm (Fin a)) (q : G →* Equiv.Perm (Fin b))
    (M : KrausChannel a b) : KrausChannel a b :=
  Classical.choose ((isChannel_iff_kraus _).mp (orbitMap_isChannel p q M))

theorem orbitChannel_map (p : G →* Equiv.Perm (Fin a)) (q : G →* Equiv.Perm (Fin b))
    (M : KrausChannel a b) : (orbitChannel p q M).toLinearMap = orbitMap p q M :=
  Classical.choose_spec ((isChannel_iff_kraus _).mp (orbitMap_isChannel p q M))

def jointPermutation (p : G →* Equiv.Perm (Fin a)) (q : G →* Equiv.Perm (Fin b)) :
    G →* Equiv.Perm (Fin a × Fin b) where
  toFun g := (p g).prodCongr (q g)
  map_one' := by ext x <;> simp
  map_mul' g h := by ext x <;> simp

theorem orbitChannel_choi (p : G →* Equiv.Perm (Fin a)) (q : G →* Equiv.Perm (Fin b))
    (M : KrausChannel a b) :
    (orbitChannel p q M).choi = weight G • ∑ g,
      Matrix.reindex (jointPermutation p q g) (jointPermutation p q g) M.choi := by
  rw [← MatrixMap.choi_toLinearMap, orbitChannel_map, orbitMap, WeightedGramMixture.choi_real_sum]
  simp only [MatrixMap.choi_toLinearMap, reindexChannel_choi, Finset.smul_sum]
  rfl

theorem orbitChannel_choi_invariant (p : G →* Equiv.Perm (Fin a))
    (q : G →* Equiv.Perm (Fin b)) (M : KrausChannel a b) (g : G) :
    Matrix.reindex (jointPermutation p q g) (jointPermutation p q g) (orbitChannel p q M).choi =
      (orbitChannel p q M).choi := by
  let e := jointPermutation p q
  have hs (h : G) (i : Fin a × Fin b) : (e (g*h)).symm i = (e h).symm ((e g).symm i) := by
    rw [map_mul]
    rfl
  rw [orbitChannel_choi]
  have hav : Matrix.reindex (e g) (e g)
      (weight G • ∑ h, Matrix.reindex (e h) (e h) M.choi) =
      weight G • ∑ h, Matrix.reindex (e (g*h)) (e (g*h)) M.choi := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sum_apply, hs]
  rw [hav]
  exact congrArg (fun X => weight G • X)
    (Equiv.sum_comp (Equiv.mulLeft g) (fun h => Matrix.reindex (e h) (e h) M.choi))

theorem orbitChannel_covariant (p : G →* Equiv.Perm (Fin a))
    (q : G →* Equiv.Perm (Fin b)) (M : KrausChannel a b) :
    Covariant p q (orbitChannel p q M) := by
  intro g X
  have hf : (reindexChannel (p g) (q g) (orbitChannel p q M)).toLinearMap =
      (orbitChannel p q M).toLinearMap := by
    apply MatrixMap.choi_injective
    simp only [MatrixMap.choi_toLinearMap,reindexChannel_choi]
    exact orbitChannel_choi_invariant p q M g
  have he := reindexChannel_apply (p g) (q g) (orbitChannel p q M) X
  change (reindexChannel (p g) (q g) (orbitChannel p q M)).toLinearMap _ = _ at he
  rw [hf] at he
  exact he


theorem singleBeta_finite_concavity {ι : Type*} [Fintype ι]
    (N A : KrausChannel a b) (M : ι → KrausChannel a b) (ε : ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hA : A.toLinearMap = ∑ i, (w i:ℂ) • (M i).toLinearMap) :
    (∑ i, ENNReal.ofReal (w i) * singleBeta N (M i) ε) ≤ singleBeta N A ε := by
  rw [singleBeta_eq_primal]
  apply le_iInf
  intro x
  have hav : testerValue x.val A.choi = ∑ i, w i*testerValue x.val (M i).choi := by
    rw [← MatrixMap.choi_toLinearMap,hA,WeightedGramMixture.choi_real_sum]
    simp [testerValue,Matrix.sum_mul,Matrix.trace_sum,Matrix.trace_smul]
  calc
    _ ≤ ∑ i, ENNReal.ofReal (w i)*ENNReal.ofReal (testerValue x.val (M i).choi) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_right
      rw [singleBeta_eq_primal]
      exact iInf_le _ x
    _ = ENNReal.ofReal (∑ i, w i*testerValue x.val (M i).choi) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (testerValue_bounds x.val x.property.1 (M i)).1)]
      simp only [ENNReal.ofReal_mul (hw _)]
    _ = _ := congrArg ENNReal.ofReal hav.symm

/-- A genuine hardest alternative can be chosen invariant under any finite physical permutation action. -/
theorem exists_symmetric_hardest (p : G →* Equiv.Perm (Fin a))
    (q : G →* Equiv.Perm (Fin b)) (N : KrausChannel a b) (ha : 0 < a)
    (hN : Covariant p q N) (F : Set (MatrixMap a b))
    (hF : ∀ M ∈ F, IsChannel M) (hc : IsCompact (MatrixMap.choi '' F))
    (hv : Convex ℝ (MatrixMap.choi '' F)) (hne : F.Nonempty)
    (hperm : ∀ g (M : KrausChannel a b), M.toLinearMap ∈ F →
      (reindexChannel (p g) (q g) M).toLinearMap ∈ F)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ M : KrausChannel a b, M.toLinearMap ∈ F ∧
      compositeBeta N F ε = singleBeta N M ε ∧ Covariant p q M := by
  obtain ⟨K,hK,hopt⟩ := lemma_5_hardest N ha F hF hc hv hne ε hε
  let A := orbitChannel p q K
  have hA : A.toLinearMap ∈ F := by
    rw [show A.toLinearMap = orbitMap p q K from orbitChannel_map p q K]
    exact WeightedGramMixture.convex_finite_mixture_mem F hv _ (fun g => hperm g K hK)
      (fun _ => weight G) (fun _ => weight_pos.le) sum_weight
  have horbit (g : G) : singleBeta N (reindexChannel (p g) (q g) K) ε = singleBeta N K ε := by
    rw [← singleBeta_reindex (p g) (q g) N K ε]
    exact singleBeta_congr _ _ _ _ ε
      (CovariantOptimization.reindexChannel_eq_of_covariant p q N hN g).symm rfl
  have hβ : singleBeta N K ε ≠ ⊤ :=
    ne_of_lt ((BranchExtraction.singleBeta_le_one N K ha ε hε).trans_lt (by simp))
  have hlow := singleBeta_mixture_lower N A (fun g => reindexChannel (p g) (q g) K) ε
    (fun _ => weight G) (fun _ => weight_pos.le) sum_weight (orbitChannel_map p q K)
    (singleBeta N K ε) hβ (fun g => (horbit g).ge)
  refine ⟨A,hA,?_,orbitChannel_covariant p q K⟩
  apply le_antisymm
  · exact hopt.le.trans hlow
  · rw [lemma_5_minimax N ha F hF hc hv hne ε hε]
    exact le_iSup_of_le ⟨A,hA⟩ le_rfl

/-- Tensor specialization assumes only F4, not the separate F5 marginal condition. -/
theorem tensor_symmetric_hardest (N : KrausChannel a b) (ha : 0 < a)
    (F : AlternativeFamily a b) (hF : Admissible F) (n : ℕ) (hn : 0 < n)
    (hperm : ∀ π : Equiv.Perm (Fin n), ∀ M : KrausChannel (a^n) (b^n),
      M.toLinearMap ∈ F n → (permuteChannel n π M).toLinearMap ∈ F n)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ M : KrausChannel (a^n) (b^n), M.toLinearMap ∈ F n ∧
      compositeBeta (N.tensorPower n) (F n) ε = singleBeta (N.tensorPower n) M ε ∧
      Covariant (TensorChannelCovariance.channelPermutation a n)
        (TensorChannelCovariance.channelPermutation b n) M := by
  exact exists_symmetric_hardest _ _ (N.tensorPower n) (pow_pos ha n)
    (TensorChannelCovariance.tensorPower_covariant N n) (F n)
    (hF.channels n hn) (hF.compact n hn) (hF.convex n hn) (hF.nonempty n hn) hperm ε hε

end GeneralizedChannelStein.SymmetricHardest
