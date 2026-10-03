import GeneralizedChannelStein.RoughApproximation
import GeneralizedChannelStein.TraceDefectCompletion

/-! # Common free dominators for subtracting prescribed-space auxiliary maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelEntropy TestingPrimal DiamondTesting TraceDefectCompletion
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- CP comparison can be multiplied by a genuine nonnegative scalar. -/
theorem cpLe_real_scale {P Q : MatrixMap a b} (h : MatrixMap.CPLe P Q)
    (t : ℝ) (ht : 0 ≤ t) : MatrixMap.CPLe ((t:ℂ) • P) ((t:ℂ) • Q) := by
  rw [MatrixMap.cpLe_iff_choi_difference] at h ⊢
  simpa only [MatrixMap.choi_smul,Complex.real_smul,← smul_sub] using h.smul ht

/-- Two free channels admit one concrete free mixture dominating both. -/
theorem exists_common_dominator (F : Set (MatrixMap a b))
    (hF : Convex ℝ (MatrixMap.choi '' F)) (M T : KrausChannel a b)
    (hM : M.toLinearMap ∈ F) (hT : T.toLinearMap ∈ F) :
    ∃ U : KrausChannel a b, U.toLinearMap ∈ F ∧
      U.toLinearMap = (1/2:ℂ) • M.toLinearMap + (1/2:ℂ) • T.toLinearMap ∧
      MatrixMap.CPLe M.toLinearMap ((2:ℂ) • U.toLinearMap) ∧
      MatrixMap.CPLe T.toLinearMap ((2:ℂ) • U.toLinearMap) := by
  obtain ⟨U,hU⟩ := (isChannel_iff_kraus _).mp
    (isChannel_combination M T (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num))
  have hU' : U.toLinearMap = (1/2:ℂ) • M.toLinearMap + (1/2:ℂ) • T.toLinearMap := by
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hU
  refine ⟨U,?_,hU',?_,?_⟩
  · rw [hU]
    exact convex_map_combination_mem F hF _ _ hM hT (1/2) (1/2)
      (by norm_num) (by norm_num) (by norm_num)
  · change MatrixMap.CompletelyPositive ((2:ℂ) • U.toLinearMap-M.toLinearMap)
    convert MatrixMap.completelyPositive_toLinearMap T using 1
    rw [hU']
    module
  · change MatrixMap.CompletelyPositive ((2:ℂ) • U.toLinearMap-T.toLinearMap)
    convert MatrixMap.completelyPositive_toLinearMap M using 1
    rw [hU']
    module

/-- Scalar CP domination composes without making a new free closure assumption. -/
theorem cpLe_through_double (L M U : MatrixMap a b) (t : ℝ) (ht : 0 ≤ t)
    (hLM : MatrixMap.CPLe L ((t:ℂ) • M))
    (hMU : MatrixMap.CPLe M ((2:ℂ) • U)) :
    MatrixMap.CPLe L (((2*t:ℝ):ℂ) • U) := by
  have h := MatrixMap.cpLe_trans hLM (cpLe_real_scale hMU t ht)
  simpa only [smul_smul,Complex.ofReal_mul,Complex.ofReal_ofNat,mul_comm] using h

/-- A positive common-dominator mixture does not worsen the rescaled testing tail. -/
theorem hockeyStick_double_dominator (N M U : KrausChannel a b) (ha : 0 < a)
    (t : ℝ) (ht : 0 ≤ t)
    (hMU : MatrixMap.CPLe M.toLinearMap ((2:ℂ) • U.toLinearMap)) :
    channelHockeyStick N U (2*t) ≤ channelHockeyStick N M t := by
  obtain ⟨ψ,T,hmax⟩ := exists_pure_maximizer N U ha (2*t)
  rw [← hmax]
  have h := testValue_le_of_cpLe M.toLinearMap U 2 hMU ψ T
  rw [testValue_channel] at h
  have htq := mul_le_mul_of_nonneg_left h ht
  have hscore := pureScore_le_channelHockeyStick N M ha t ψ T
  dsimp [pureScore] at hscore ⊢
  linarith

end GeneralizedChannelStein
