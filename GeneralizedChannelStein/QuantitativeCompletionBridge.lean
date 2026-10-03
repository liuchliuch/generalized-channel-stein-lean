import GeneralizedChannelStein.IsometricCompletionStatement
import GeneralizedChannelStein.LiftedBranch
import GeneralizedChannelStein.FixedDilation
import GeneralizedChannelStein.LiftedReplacerBound
import GeneralizedChannelStein.CompletionPrefactor
import GeneralizedChannelStein.PostprocessingBounds

/-! Completion for noisy channels from actual isometric completion and fixed-size dilations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix BranchExtraction
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

theorem cpLe_scale_mono (L : KrausChannel a b) (r s : ℝ) (hrs : r≤s) :
    MatrixMap.CPLe ((r:ℂ) • L.toLinearMap) ((s:ℂ) • L.toLinearMap) := by
  have h := MatrixMap.completelyPositive_smul (sub_nonneg.mpr hrs)
    (MatrixMap.completelyPositive_toLinearMap L)
  change MatrixMap.CompletelyPositive ((s:ℂ) • L.toLinearMap-(r:ℂ) • L.toLinearMap)
  have he : (((s-r:ℝ):ℂ) • L.toLinearMap)=(s:ℂ) • L.toLinearMap-(r:ℂ) • L.toLinearMap := by
    ext X i j
    change (((s-r:ℝ):ℂ) * L.apply X i j)=(s:ℂ)*L.apply X i j-(r:ℂ)*L.apply X i j
    rw [Complex.ofReal_sub,sub_mul]
  rw [←he]
  exact h

theorem completionOverlap_le_one (ε : ℝ) : completionOverlap ε≤1 := by
  unfold completionOverlap
  apply (div_le_one (by positivity)).mpr
  linarith [Real.sqrt_nonneg (1-ExtensionComparison.tolerance ε)]

/-- This implication is a proved construction; the final theorem supplies hIso from Proposition 30. -/
theorem completion_of_isometric_property (ha : 0<a) (hb : 0<b)
    (t w ε K : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (hIso : IsometricCompletionProperty a (b*(a*b)) t (w/(a*b:ℕ)) (completionOverlap ε) K)
    (N : KrausChannel a b) (F : AlternativeFamily a b) (hF : Admissible F)
    (τ : State a) (hQ : QuantitativeAt F τ) (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (hτt : (τ.matrix-t•(1:Operator a)).PosSemidef)
    (hωw : (ω.matrix-w•(1:Operator b)).PosSemidef) :
    CompletionProperty N F ε (CompletionPrefactor.adjustedConstant K (ExtensionComparison.factor ε)) := by
  refine ⟨CompletionPrefactor.adjustedConstant_nonneg hIso.nonnegative _,?_⟩
  intro n hn δ hδ hδ1
  have he : 0<a*b := Nat.mul_pos ha hb
  obtain ⟨V,hV,hVN⟩ := FixedDilation.exists_fixed_dilation N
  obtain ⟨p,M,Z,hp,hp1,hM,hZn,hZo,hZcp,hpb⟩ := lifted_testing_branch N ha hb F hF ω hω hOne
    he V hV hVN n hn ε hε hε1
  let G := liftedFamily F (a*b)
  let η := liftedReplacer ω he
  have hηmem : ((ReplacerChannel.channel a η).tensorPower 1).toLinearMap∈G 1 := by
    refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
    change ((AuxiliaryExtensions.discard b (a*b)).tensorPower 1).toLinearMap.comp
      ((ReplacerChannel.channel a η).tensorPower 1).toLinearMap∈F 1
    rw [post_replacer_power _ η ω (discard_tensorState ω _) 1]
    exact hOne
  obtain ⟨L,S,hS,hdom,hclose⟩ := hIso.complete G (liftedFamily_admissible F hF ω hω hOne he)
    τ (liftedFamily_quantitative F τ hQ (a*b)) η hηmem hτt
    (LiftedReplacerBound.liftedReplacer_lower ω he w hωw)
    (AuxiliaryExtensions.outputIsometry V) (AuxiliaryExtensions.outputIsometry_isometry V hV)
    n hn M hM Z p hp hp1 hZn hZo hZcp δ hδ hδ1
  have htarget : (((AuxiliaryExtensions.discard b (a*b)).tensorPower n).compose
      (liftedTarget V hV n)).toLinearMap=(N.tensorPower n).toLinearMap := by
    rw [compose_map]
    exact reduce_liftedTarget N V hV hVN n
  have hcl : DiamondNorm.diamondNorm (L.toLinearMap-(liftedTarget V hV n).toLinearMap)≤ENNReal.ofReal δ := by
    change DiamondNorm.diamondNorm (L.toLinearMap-(isometryChannel _ _).toLinearMap)≤_ 
    rw [benchmark_isometry_map]
    exact hclose
  obtain ⟨L',S',hS',hdom',hclose'⟩ := PostprocessingBounds.postprocess_approximation
    ((AuxiliaryExtensions.discard b (a*b)).tensorPower n) L (liftedTarget V hV n) S
    (N.tensorPower n) (F n) _ _ htarget hS.2 hdom hcl
  refine ⟨L',S',hS',?_,hclose'⟩
  have hfac := (ExtensionComparison.parameters ε hε hε1).2.2
  have hc := CompletionPrefactor.absorb_prefactor hfac hpb (ENNReal.toReal_nonneg)
    hn hδ hδ1 (K:=K)
  exact MatrixMap.cpLe_trans (cpLe_scale_mono L' _ _ hc) hdom'

end GeneralizedChannelStein
