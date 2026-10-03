import GeneralizedChannelStein.PrimalTesting

/-! # Composite testing minimax in genuine compact Choi coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy TestingSDP TestingPrimal Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {a b : ℕ}

/-- The exact Sion exchange on the physical tester set and a compact convex
set of alternative Choi matrices. Neither order is used as a definition of the other. -/
theorem choi_testing_minimax (N : KrausChannel a b) (ha : 0 < a)
    (ε : ℝ) (hε : 0 ≤ ε) (C : Set (BipartiteOperator a b))
    (hc : IsCompact C) (hconv : Convex ℝ C) (hne : C.Nonempty) :
    (⨅ x : testerSet N ε, ⨆ M : C, testerValue x.val M.val) =
    (⨆ M : C, ⨅ x : testerSet N ε, testerValue x.val M.val) := by
  apply sion_minimax (f := fun x M => testerValue x M) (S := testerSet N ε) (T := C)
  · intro M _
    have h : Continuous (fun x : Operator a × BipartiteOperator a b => testerValue x M) := by
      unfold testerValue Matrix.trace Matrix.diag
      fun_prop
    exact h.lowerSemicontinuous.lowerSemicontinuousOn _
  · exact isCompact_testerSet N ε
  · exact testerSet_nonempty N ha ε hε
  · exact hne
  · intro x _
    have h : Continuous (testerValue x) := by
      unfold testerValue Matrix.trace Matrix.diag
      fun_prop
    exact h.upperSemicontinuous.upperSemicontinuousOn _
  · intro M _
    apply ConvexOn.quasiconvexOn
    refine ⟨convex_testerSet N ε, ?_⟩
    intro x _ y _ r s _ _ _
    exact (testerValue_mix_left x y M r s).le
  · intro x _
    apply ConcaveOn.quasiconcaveOn
    refine ⟨hconv, ?_⟩
    intro M _ K _ r s _ _ _
    exact (testerValue_mix_right x M K r s).ge
  · exact hconv
  · exact convex_testerSet N ε
  · rw [← Set.image_prod]
    exact ((isCompact_testerSet N ε).prod hc).bddAbove_image
      (continuous_testerValue (a := a) (b := b)).continuousOn
  · rw [← Set.image_prod]
    exact ((isCompact_testerSet N ε).prod hc).bddBelow_image
      (continuous_testerValue (a := a) (b := b)).continuousOn

/-- Compactness bounds the inner optimization even on arbitrary Hermitian objectives. -/
theorem testerValue_range_bddBelow (N : KrausChannel a b) (ε : ℝ)
    (C : BipartiteOperator a b) :
    BddBelow (Set.range (fun x : testerSet N ε => testerValue x.val C)) := by
  have h : Continuous (fun x : Operator a × BipartiteOperator a b => testerValue x C) := by
    unfold testerValue Matrix.trace Matrix.diag
    fun_prop
  apply ((isCompact_testerSet N ε).bddBelow_image h.continuousOn).mono
  rintro _ ⟨x,rfl⟩
  exact ⟨x.val,x.property,rfl⟩

/-- The hardest Choi alternative exists; its tester optimum is upper semicontinuous. -/
theorem exists_hardest_choi (N : KrausChannel a b) (ε : ℝ)
    (C : Set (BipartiteOperator a b)) (hc : IsCompact C) (hne : C.Nonempty) :
    ∃ M ∈ C, ∀ K ∈ C,
      (⨅ x : testerSet N ε, testerValue x.val K) ≤
      (⨅ x : testerSet N ε, testerValue x.val M) := by
  have hsc : UpperSemicontinuous
      (fun M : BipartiteOperator a b => ⨅ x : testerSet N ε, testerValue x.val M) := by
    apply upperSemicontinuous_ciInf
    · intro M
      exact testerValue_range_bddBelow N ε M
    · intro x
      have h : Continuous (testerValue x.val) := by
        unfold testerValue Matrix.trace Matrix.diag
        fun_prop
      exact h.upperSemicontinuous
  exact (hsc.upperSemicontinuousOn C).exists_isMaxOn hne hc

end GeneralizedChannelStein
