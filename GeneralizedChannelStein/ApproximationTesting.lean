import GeneralizedChannelStein.UniformBounds
import GeneralizedChannelStein.TraceDefectCompletion

/-! # One-shot testing consequences of exact trace-preserving approximation -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy OperationalTesting DiamondNorm DiamondTesting
open UniformAuxiliary ParallelTestingReduction
variable {a b : ℕ}

/-- A single exact-TP approximation controls every mixed arbitrary-reference
input and effect. The factor 1/2 uses the full unhalved diamond norm. -/
theorem test_acceptance_le_approximation (N L M : KrausChannel a b)
    (c δ : ℝ) (hδ : 0 ≤ δ)
    (hdom : MatrixMap.CPLe L.toLinearMap ((c:ℂ) • M.toLinearMap))
    (hclose : diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ)
    (t : ChannelTest a b) : t.acceptance N ≤ δ/2+c*t.acceptance M := by
  obtain ⟨ψ,T,h⟩ := exists_pure_test t
  have hd := probability_sub_le_half_diamond N L δ hδ hclose ψ T
  have hc := testValue_le_of_cpLe L.toLinearMap M c hdom ψ T
  rw [testValue_channel] at hc
  rw [h,h] at hd
  rw [h,h] at hc
  linarith

/-- The chosen dominator precedes all tests; the resulting lower bound is uniform. -/
theorem compositeBeta_lower_of_approximation (N L M : KrausChannel a b)
    (F : Set (MatrixMap a b)) (hM : M.toLinearMap ∈ F)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ)
    (hdom : MatrixMap.CPLe L.toLinearMap ((c:ℂ) • M.toLinearMap))
    (hclose : diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ)
    (ε : ℝ) : ENNReal.ofReal ((1-ε-δ/2)/c) ≤ compositeBeta N F ε := by
  apply le_iInf
  intro t
  have h := test_acceptance_le_approximation N L M c δ hδ hdom hclose t.val
  have hq : (1-ε-δ/2)/c ≤ t.val.acceptance M :=
    (div_le_iff₀ hc).mpr (by linarith [t.property])
  exact (ENNReal.ofReal_le_ofReal hq).trans (acceptance_le_worst F t.val M hM)

/-- One-shot perturbation sandwich, valid for correlated targets as well. -/
theorem compositeBeta_perturbation_lower (N L : KrausChannel a b)
    (F : Set (MatrixMap a b)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ)
    (ε : ℝ) : compositeBeta N F (ε+δ/2) ≤ compositeBeta L F ε := by
  apply le_iInf
  intro t
  have hsym : diamondNorm (N.toLinearMap-L.toLinearMap) ≤ ENNReal.ofReal δ := by
    rw [← neg_sub L.toLinearMap N.toLinearMap, DiamondNorm.diamondNorm_neg]
    exact hclose
  have h := test_acceptance_le_approximation L N N 1 δ hδ
    (by simpa using MatrixMap.cpLe_refl N.toLinearMap) hsym t.val
  refine iInf_le_of_le ⟨t.val,?_⟩ le_rfl
  linarith [t.property]

end GeneralizedChannelStein
