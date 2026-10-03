import Paper.Statements
import GeneralizedChannelStein

/-! Proofs of the separately stated paper contracts. -/
namespace GeneralizedChannelStein.Paper

theorem theorem_2 : PaperStatements.theorem_2 :=
  @GeneralizedChannelStein.theorem_2

theorem theorem_3 : PaperStatements.theorem_3 :=
  @GeneralizedChannelStein.theorem_3

theorem lemma_4 : PaperStatements.lemma_4 :=
  @GeneralizedChannelStein.lemma_4

theorem lemma_5_minimax : PaperStatements.lemma_5_minimax :=
  @GeneralizedChannelStein.lemma_5_minimax

theorem lemma_5_hardest : PaperStatements.lemma_5_hardest :=
  @GeneralizedChannelStein.lemma_5_hardest

theorem lemma_5_optimal_tester : PaperStatements.lemma_5_optimal_tester :=
  @GeneralizedChannelStein.lemma_5_optimal_tester

theorem lemma_6_testing : PaperStatements.lemma_6_testing :=
  @GeneralizedChannelStein.UniformAuxiliary.lemma_6_testing

theorem lemma_6_diamond : PaperStatements.lemma_6_diamond :=
  @GeneralizedChannelStein.UniformAuxiliary.lemma_6_diamond

theorem lemma_6_exact : PaperStatements.lemma_6_exact :=
  @GeneralizedChannelStein.UniformAuxiliary.lemma_6_exact

theorem lemma_6_converse : PaperStatements.lemma_6_converse :=
  @GeneralizedChannelStein.UniformAuxiliary.lemma_6_converse

theorem lemma_7 : PaperStatements.lemma_7 :=
  @GeneralizedChannelStein.TraceDefectCompletion.lemma_7

theorem proposition_8_unbounded : PaperStatements.proposition_8_unbounded :=
  @GeneralizedChannelStein.FreeAmplification.proposition_8_unbounded

theorem proposition_9 : PaperStatements.proposition_9 :=
  @GeneralizedChannelStein.proposition_9

theorem lemma_10 : PaperStatements.lemma_10 :=
  @GeneralizedChannelStein.EntropyComparison.lemma_10

theorem theorem_11 : PaperStatements.theorem_11 :=
  @GeneralizedChannelStein.theorem_11

theorem theorem_11_extended : PaperStatements.theorem_11_extended :=
  @GeneralizedChannelStein.theorem_11_extended

theorem theorem_12 : PaperStatements.theorem_12 :=
  @GeneralizedChannelStein.theorem_12

theorem corollary_13 : PaperStatements.corollary_13 :=
  @GeneralizedChannelStein.corollary_13

theorem theorem_16_uniform_lowerBounds : PaperStatements.theorem_16_uniform_lowerBounds :=
  @GeneralizedChannelStein.theorem_16_uniform_lowerBounds

theorem theorem_16 : PaperStatements.theorem_16 :=
  @GeneralizedChannelStein.theorem_16

theorem corollary_17 : PaperStatements.corollary_17 :=
  @GeneralizedChannelStein.corollary_17

theorem corollary_17_lower : PaperStatements.corollary_17_lower :=
  @GeneralizedChannelStein.corollary_17_lower

theorem lemma_18 : PaperStatements.lemma_18 :=
  @GeneralizedChannelStein.lemma_18

theorem lemma_18_normalized : PaperStatements.lemma_18_normalized :=
  @GeneralizedChannelStein.lemma_18_normalized

theorem proposition_19_complete : PaperStatements.proposition_19_complete :=
  @GeneralizedChannelStein.proposition_19_complete

theorem stateBeta_attained : PaperStatements.stateBeta_attained :=
  @GeneralizedChannelStein.stateBeta_attained

theorem proposition_20 : PaperStatements.proposition_20 :=
  @GeneralizedChannelStein.proposition_20

theorem mem_MIOFamily_iff_map : PaperStatements.mem_MIOFamily_iff_map :=
  @GeneralizedChannelStein.MIOOperational.mem_MIOFamily_iff_map

theorem proposition_21 : PaperStatements.proposition_21 :=
  @GeneralizedChannelStein.proposition_21

theorem intersection_admissible : PaperStatements.intersection_admissible :=
  @GeneralizedChannelStein.intersection_admissible

theorem intersection_quantitative : PaperStatements.intersection_quantitative :=
  @GeneralizedChannelStein.intersection_quantitative

theorem proposition_22_families : PaperStatements.proposition_22_families :=
  @GeneralizedChannelStein.proposition_22_families

theorem proposition_22_benchmarks : PaperStatements.proposition_22_benchmarks :=
  @GeneralizedChannelStein.proposition_22_benchmarks

theorem corollary_23 : PaperStatements.corollary_23 :=
  @GeneralizedChannelStein.corollary_23

theorem example_24 : PaperStatements.example_24 :=
  @GeneralizedChannelStein.Correlated.example_24

theorem alternativeFamily_one : PaperStatements.alternativeFamily_one :=
  @GeneralizedChannelStein.Correlated.alternativeFamily_one

theorem generator_block_formula : PaperStatements.generator_block_formula :=
  @GeneralizedChannelStein.Correlated.generator_block_formula

theorem lemma_25 : PaperStatements.lemma_25 :=
  @GeneralizedChannelStein.BranchExtraction.lemma_25

theorem lemma_26 : PaperStatements.lemma_26 :=
  @GeneralizedChannelStein.ExtensionComparison.lemma_26

theorem lemma_27 : PaperStatements.lemma_27 :=
  @GeneralizedChannelStein.lemma_27

theorem lemma_28 : PaperStatements.lemma_28 :=
  @GeneralizedChannelStein.FreeMultipliers.lemma_28

theorem lemma_29 : PaperStatements.lemma_29 :=
  @GeneralizedChannelStein.ImageProjector.lemma_29

theorem proposition_30 : PaperStatements.proposition_30 :=
  @GeneralizedChannelStein.IsometricCompletion.proposition_30

theorem proposition_30_minEigen : PaperStatements.proposition_30_minEigen :=
  @GeneralizedChannelStein.IsometricCompletion.proposition_30_minEigen

theorem value_concave_input : PaperStatements.value_concave_input :=
  @GeneralizedChannelStein.CanonicalConcavity.value_concave_input

theorem value_convex_alternative : PaperStatements.value_convex_alternative :=
  @GeneralizedChannelStein.EntropyMinimax.value_convex_alternative

theorem lemma_32 : PaperStatements.lemma_32 :=
  @GeneralizedChannelStein.EntropyMinimaxResults.lemma_32

theorem lemma_32_permutation_optimizer : PaperStatements.lemma_32_permutation_optimizer :=
  @GeneralizedChannelStein.EntropyMinimaxResults.lemma_32_permutation_optimizer

theorem lemma_33 : PaperStatements.lemma_33 :=
  @GeneralizedChannelStein.NearSubadditiveEntropy.lemma_33

theorem lemma_34 : PaperStatements.lemma_34 :=
  @GeneralizedChannelStein.NearSubadditive.lemma_34

theorem appendix_b_theorem_2 : PaperStatements.appendix_b_theorem_2 :=
  @GeneralizedChannelStein.AppendixTestingLimit.appendix_b_theorem_2

theorem isChannel_iff_kraus : PaperStatements.isChannel_iff_kraus :=
  @GeneralizedChannelStein.isChannel_iff_kraus

theorem compositeBeta_eq_pure : PaperStatements.compositeBeta_eq_pure :=
  @GeneralizedChannelStein.compositeBeta_eq_pure

theorem admissible_values_finite : PaperStatements.admissible_values_finite :=
  @GeneralizedChannelStein.admissible_values_finite

end GeneralizedChannelStein.Paper
