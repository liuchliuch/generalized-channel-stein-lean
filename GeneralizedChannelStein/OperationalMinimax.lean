import GeneralizedChannelStein.PrimalBeta

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy TestingSDP TestingPrimal Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {a b : ℕ}

/-- A bounded minimax identity is preserved on passing to extended probabilities. -/
theorem ofReal_minimax {X Y : Type*} [Nonempty X] [Nonempty Y]
    (f : X → Y → ℝ) (hb : ∀ x y, f x y ≤ 1)
    (h : (⨅ x, ⨆ y, f x y) = (⨆ y, ⨅ x, f x y)) :
    (⨅ x, ⨆ y, ENNReal.ofReal (f x y)) =
    (⨆ y, ⨅ x, ENNReal.ofReal (f x y)) := by
  have hbSup : ∀ x, BddAbove (Set.range (f x)) := by
    intro x
    exact ⟨1,by rintro _ ⟨y,rfl⟩; exact hb x y⟩
  have hbInf : BddAbove (Set.range (fun y => ⨅ x, f x y)) := by
    refine ⟨1,?_⟩
    rintro _ ⟨y,rfl⟩
    by_cases hh : BddBelow (Set.range (fun x => f x y))
    · exact (ciInf_le hh (Classical.arbitrary X)).trans (hb _ _)
    · change (⨅ x, f x y) ≤ 1
      rw [Real.iInf_of_not_bddBelow hh]
      norm_num
  calc
    _ = ENNReal.ofReal (⨅ x, ⨆ y, f x y) := by
      rw [ENNReal.ofReal_iInf]
      simp_rw [ofReal_ciSup _ (hbSup _)]
    _ = ENNReal.ofReal (⨆ y, ⨅ x, f x y) := congrArg ENNReal.ofReal h
    _ = _ := by
      rw [ofReal_ciSup _ hbInf]
      simp_rw [ENNReal.ofReal_iInf]

/-- The compact Choi minimax identity now has the exact probability codomain. -/
theorem choiBeta_minimax (N : KrausChannel a b) (ha : 0 < a)
    (ε : ℝ) (hε : 0 ≤ ε) (C : Set (BipartiteOperator a b))
    (hc : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hchannels : ∀ M ∈ C, ∃ K : KrausChannel a b, K.choi = M) :
    choiBeta N C ε = ⨆ M : C, ⨅ x : testerSet N ε,
      ENNReal.ofReal (testerValue x.val M.val) := by
  letI : Nonempty (testerSet N ε) := (testerSet_nonempty N ha ε hε).to_subtype
  letI : Nonempty C := hne.to_subtype
  apply ofReal_minimax
  · intro x M
    obtain ⟨K,hK⟩ := hchannels M.val M.property
    rw [← hK]
    exact (testerValue_bounds x.val x.property.1 K).2
  · exact choi_testing_minimax N ha ε hε C hc hconv hne

/-- Lemma 5, the genuine operational inf-tester/sup-alternative exchange. -/
theorem lemma_5_minimax (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (hF : ∀ M ∈ F, IsChannel M)
    (hc : IsCompact (MatrixMap.choi '' F)) (hv : Convex ℝ (MatrixMap.choi '' F))
    (hne : F.Nonempty) (ε : ℝ) (hε : 0 ≤ ε) :
    compositeBeta N F ε = ⨆ M : FreeChannel F, singleBeta N M.val ε := by
  rw [compositeBeta_eq_primal, primalBeta_eq_choiBeta N F hF ε,
    choiBeta_minimax N ha ε hε _ hc hv (hne.image _)]
  · simp_rw [singleBeta_eq_primal]
    apply le_antisymm
    · apply iSup_le
      intro C
      obtain ⟨M,hM,hC⟩ := C.property
      obtain ⟨K,hK⟩ := (isChannel_iff_kraus M).mp (hF M hM)
      refine le_iSup_of_le ⟨K,hK ▸ hM⟩ ?_
      have he : K.choi = C.val := by rw [← MatrixMap.choi_toLinearMap,hK,hC]
      simp only [primalSingleBeta,he,le_refl]
    · apply iSup_le
      intro M
      exact le_iSup_of_le ⟨M.val.choi, M.val.toLinearMap,M.property,rfl⟩ le_rfl
  · rintro C ⟨M,hM,rfl⟩
    obtain ⟨K,hK⟩ := (isChannel_iff_kraus M).mp (hF M hM)
    exact ⟨K,by rw [← MatrixMap.choi_toLinearMap,hK]⟩

/-- Lemma 5, there is one hardest free alternative, selected independently of the tester. -/
theorem lemma_5_hardest (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (hF : ∀ M ∈ F, IsChannel M)
    (hc : IsCompact (MatrixMap.choi '' F)) (hv : Convex ℝ (MatrixMap.choi '' F))
    (hne : F.Nonempty) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ M : KrausChannel a b, M.toLinearMap ∈ F ∧
      compositeBeta N F ε = singleBeta N M ε := by
  letI : Nonempty (testerSet N ε) := (testerSet_nonempty N ha ε hε).to_subtype
  obtain ⟨C,hC,hmax⟩ := exists_hardest_choi N ε (MatrixMap.choi '' F) hc (hne.image _)
  obtain ⟨M,hM,hMC⟩ := hC
  obtain ⟨K,hK⟩ := (isChannel_iff_kraus M).mp (hF M hM)
  have hKC : K.choi = C := by rw [← MatrixMap.choi_toLinearMap,hK,hMC]
  refine ⟨K,hK ▸ hM,?_⟩
  rw [lemma_5_minimax N ha F hF hc hv hne ε hε]
  apply le_antisymm
  · apply iSup_le
    intro L
    simp only [singleBeta_eq_primal,primalSingleBeta, ← ENNReal.ofReal_iInf]
    apply ENNReal.ofReal_le_ofReal
    rw [hKC]
    exact hmax L.val.choi ⟨L.val.toLinearMap,L.property,rfl⟩
  · exact le_iSup_of_le ⟨K,hK ▸ hM⟩ le_rfl

/-- Lemma 5, a single optimum tester exists for the whole alternative family.
This attainment needs no family compactness: a supremum of continuous acceptance
functions is lower semicontinuous on the compact physical tester domain. -/
theorem lemma_5_optimal_tester (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ ψ : UnitPureInput a a, ∃ T : Effect (a*b),
      1-ε ≤ T.probability (pureOutput N ψ) ∧
      compositeBeta N F ε =
        ⨆ M : FreeChannel F, ENNReal.ofReal (T.probability (pureOutput M.val ψ)) := by
  have hsc : LowerSemicontinuous
      (fun x : Operator a × BipartiteOperator a b =>
        ⨆ M : FreeChannel F, ENNReal.ofReal (testerValue x M.val.choi)) := by
    apply lowerSemicontinuous_iSup
    intro M
    have h : Continuous (fun x : Operator a × BipartiteOperator a b =>
        testerValue x M.val.choi) := by
      unfold testerValue Matrix.trace Matrix.diag
      fun_prop
    exact (ENNReal.continuous_ofReal.comp h).lowerSemicontinuous
  obtain ⟨x,hx,hmin⟩ := (hsc.lowerSemicontinuousOn (testerSet N ε)).exists_isMinOn
    (testerSet_nonempty N ha ε hε) (isCompact_testerSet N ε)
  obtain ⟨ψ,T,h⟩ := exists_uniform_primal_realization (primalOfMem x hx.1)
  refine ⟨ψ,T,?_,?_⟩
  · rw [h]
    exact hx.2
  · rw [compositeBeta_eq_primal]
    simp only [h]
    apply le_antisymm
    · exact iInf_le_of_le ⟨x,hx⟩ le_rfl
    · apply le_iInf
      intro y
      exact hmin y.property

end GeneralizedChannelStein
