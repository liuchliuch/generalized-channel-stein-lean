import GeneralizedChannelStein.AppendixTestingLimit
import Lean.Util.CollectAxioms

/-! Check that the Appendix B proof uses its constructive route. -/
set_option maxHeartbeats 0
open Lean in
run_cmd do
  let env ← getEnv
  let (_, s) := ((CollectAxioms.collect
    `GeneralizedChannelStein.AppendixTestingLimit.appendix_b_theorem_2).run env).run {}
  let forbidden : Array Name := #[
    `GeneralizedChannelStein.testing_limit,
    `GeneralizedChannelStein.testing_limit_extended,
    `GeneralizedChannelStein.entropy_limit,
    `GeneralizedChannelStein.entropy_liminf_ge_steinRate,
    `GeneralizedChannelStein.entropy_limsup_le_steinRate,
    `GeneralizedChannelStein.entropy_limsup_le_strict_rate,
    `GeneralizedChannelStein.exponential_above_steinRate,
    `GeneralizedChannelStein.limsup_le_liminf_testing,
    `GeneralizedChannelStein.lowerTestingRate_eq,
    `GeneralizedChannelStein.proposition_9,
    `GeneralizedChannelStein.theorem_2,
    `GeneralizedChannelStein.theorem_3]
  for n in forbidden do
    if s.visited.contains n then
      throwError "Unexpected original main-route dependency: {n}"
  let required : Array Name := #[
    `GeneralizedChannelStein.theorem_16_exists,
    `GeneralizedChannelStein.AppendixTestingLimit.completed_product,
    `GeneralizedChannelStein.TensorDiamond.tensorBlocks_difference_le,
    `GeneralizedChannelStein.NearSubadditive.exists_limit_of_power_error,
    `GeneralizedChannelStein.lemma_18_normalized,
    `GeneralizedChannelStein.lemma_4,
    `GeneralizedChannelStein.NearSubadditiveEntropy.lemma_33_entropy_form,
    `GeneralizedChannelStein.AppendixCompletionScalars.exists_fixed_radius_envelope]
  for n in required do
    unless s.visited.contains n do
      throwError "Expected constructive Appendix dependency absent: {n}"
  logInfo "PASS: all eight required constructive dependencies present; twelve original main-route endpoints/helpers absent"
