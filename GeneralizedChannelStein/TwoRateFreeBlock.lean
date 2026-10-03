import GeneralizedChannelStein.CommonDominator
import QuantumChannelStein.TwoRateBlock

/-! # A two-rate tensor construction with a varying free dominator

All maps and tensor words are concrete matrices. The error and scalar norm
premises are local finite-block input data, later discharged from testing and
an exponential approximation. No family approximation conclusion is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelEntropy TestingPrimal UniformAuxiliary
  TensorPower EnvironmentTensor UniformApproximation ParallelConverse
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder
variable {a b : ℕ}

/-- One free mixture supplies both auxiliary maps in exactly the same spaces;
therefore their difference is the residual used in the tensor expansion. -/
theorem two_rate_common_auxiliary (N M T L : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (hF : Convex ℝ (MatrixMap.choi '' F))
    (hM : M.toLinearMap ∈ F) (hT : T.toLinearMap ∈ F)
    (t lam d e r s η z : ℝ) (k m : ℕ)
    (ht : 0 ≤ t) (hlam : 0 ≤ lam) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hrough : channelHockeyStick N M t ≤ d^2)
    (hdom : MatrixMap.CPLe L.toLinearMap ((lam:ℂ) • T.toLinearMap))
    (hclose : DiamondNorm.diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal (2*e^2))
    (hsmall : e ≤ (1-d)/2) (hrs : r ≤ s) (hz : 1 ≤ z)
    (hcostA : Real.sqrt (2*t) ≤ (2:ℝ)^((k:ℝ)*r/2))
    (hcostB : Real.sqrt (2*lam) ≤ (2:ℝ)^((k:ℝ)*s/2)) :
    ∃ U : KrausChannel a b, U.toLinearMap ∈ F ∧
      ∃ A : Matrix (Index (Fin N.rank) m) (Index (Fin U.rank) m) ℂ,
      ‖A‖ ≤ 3^m*(2:ℝ)^((k:ℝ)*m*(r+η*(s-r))/2) ∧
      ‖blockDilation N.stinespring m-applyEnvironment (blockDilation U.stinespring m) A‖ ≤
        z^(-(η*m))*(1+d+z*((1+d)/2))^m+(m:ℝ)*e*(1+e)^(m-1) := by
  obtain ⟨U,hU,_,hMU,hTU⟩ := exists_common_dominator F hF M T hM hT
  have hh := (hockeyStick_double_dominator N M U ha t ht hMU).trans hrough
  obtain ⟨A,hA,hea⟩ := lemma_6_testing N U ha N.stinespring U.stinespring
    (dilationMap_stinespring N) (dilationMap_stinespring U) (2*t) (by positivity)
  have hAnorm : ‖A‖ ≤ (2:ℝ)^((k:ℝ)*r/2) := hA.trans hcostA
  have hAe : ‖N.stinespring-((1:Operator b) ⊗ₖ A)*U.stinespring‖ ≤ d := by
    have h := hea.trans hh
    nlinarith [norm_nonneg (N.stinespring-((1:Operator b) ⊗ₖ A)*U.stinespring)]
  have hstrong := cpLe_through_double L.toLinearMap T.toLinearMap U.toLinearMap lam hlam hdom hTU
  obtain ⟨B,hB,heb⟩ := lemma_6_diamond N U L ha N.stinespring U.stinespring
    (dilationMap_stinespring N) (dilationMap_stinespring U) (2*lam) (2*e^2)
    (by positivity) (by positivity) hstrong hclose
  have hBnorm : ‖B‖ ≤ (2:ℝ)^((k:ℝ)*s/2) := hB.trans hcostB
  have hBe : ‖N.stinespring-((1:Operator b) ⊗ₖ B)*U.stinespring‖ ≤ e := by
    nlinarith [norm_nonneg (N.stinespring-((1:Operator b) ⊗ₖ B)*U.stinespring)]
  obtain ⟨C,hC,herr⟩ := TwoRateBlock.two_rate_block_auxiliary
    N.stinespring U.stinespring A B k m r s d e η z
    (norm_isometry_le_one N.stinespring N.stinespring_isometry)
    hAe hBe he hd hsmall hrs hz hAnorm hBnorm
  exact ⟨U,hU,C,hC,herr⟩

end GeneralizedChannelStein
