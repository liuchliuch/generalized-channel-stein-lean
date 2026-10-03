import GeneralizedChannelStein.TwoRateFreeBlock
import GeneralizedChannelStein.FreeAmplification

/-! # Exact-TP completion of the new two-rate free block construction -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelEntropy TestingPrimal UniformAuxiliary
  TensorPower EnvironmentTensor UniformApproximation ParallelConverse
  RepeatedBlocks FreeAmplification StatePowerRenyi PerfectDiscrimination
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder
variable {a b : ℕ}

/-- Replacer powers are literally the channel preparing the product density. -/
theorem product_replacer_mem (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0 < n) :
    (ReplacerChannel.channel (a^n) (statePower ω n)).toLinearMap ∈ F n := by
  rw [ReplacerChannel.channel_map, ← ReplacerChannel.tensorPower_map (n := a)]
  exact replacer_power_mem F hF.tensor_closed ω hOne n hn

/-- Both truncation and exact trace completion preserve the free family at km.
All scalar bounds are explicit; the same free map controls every reference/input. -/
theorem two_rate_completed_block (N : KrausChannel a b) (ha : 0 < a)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (M T L : KrausChannel (a^k) (b^k)) (hM : M.toLinearMap ∈ F k) (hT : T.toLinearMap ∈ F k)
    (t lam d e r s η z c : ℝ)
    (ht : 0 ≤ t) (hlam : 0 ≤ lam) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hrough : channelHockeyStick (N.tensorPower k) M t ≤ d^2)
    (hdom : MatrixMap.CPLe L.toLinearMap ((lam:ℂ) • T.toLinearMap))
    (hclose : DiamondNorm.diamondNorm (L.toLinearMap-(N.tensorPower k).toLinearMap) ≤
      ENNReal.ofReal (2*e^2))
    (hsmall : e ≤ (1-d)/2) (hrs : r ≤ s) (hz : 1 ≤ z)
    (hcostA : Real.sqrt (2*t) ≤ (2:ℝ)^((k:ℝ)*r/2))
    (hcostB : Real.sqrt (2*lam) ≤ (2:ℝ)^((k:ℝ)*s/2))
    (hc : 1 ≤ c) (hcost : (3^m*(2:ℝ)^((k:ℝ)*m*(r+η*(s-r))/2))^2 ≤ c) :
    ∃ L' S : KrausChannel (a^(k*m)) (b^(k*m)), S.toLinearMap ∈ F (k*m) ∧
      MatrixMap.CPLe L'.toLinearMap (((c+1:ℝ):ℂ) • S.toLinearMap) ∧
      DiamondNorm.diamondNorm (L'.toLinearMap-(N.tensorPower (k*m)).toLinearMap) ≤
        ENNReal.ofReal (8*(z^(-(η*m))*(1+d+z*((1+d)/2))^m+(m:ℝ)*e*(1+e)^(m-1))) := by
  obtain ⟨U,hU,A,hA,herr⟩ := two_rate_common_auxiliary (N.tensorPower k) M T L (pow_pos ha k)
    (F k) (hF.convex k hk) hM hT t lam d e r s η z k m ht hlam hd he hrough hdom hclose
    hsmall hrs hz hcostA hcostB
  apply complete_repeated_auxiliary N F ha k m U (hF.convex (k*m) (Nat.mul_pos hk hm))
    (repeatBlock_mem F hF.tensor_closed k hk U hU m hm) (statePower ω (k*m))
    (product_replacer_mem F hF ω hOne (k*m) (Nat.mul_pos hk hm))
    (N.tensorPower k).stinespring U.stinespring (N.tensorPower k).stinespring_isometry
    (dilationMap_stinespring _) (dilationMap_stinespring _) A c _ hc
  · positivity
  · exact (pow_le_pow_left₀ (norm_nonneg A) hA 2).trans hcost
  · exact herr

end GeneralizedChannelStein
