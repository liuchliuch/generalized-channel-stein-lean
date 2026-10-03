import GeneralizedChannelStein.FreeAmplification
import GeneralizedChannelStein.CorrectedBranch

/-! Trace-preserving completion of a genuinely dominated close branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CloseBranchCompletion
open QuantumChannelStein Matrix ChannelEntropy BranchExtraction
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

theorem cpLe_smul {P Q : MatrixMap a b} (h : MatrixMap.CPLe P Q) {s : ℝ} (hs : 0≤s) :
    MatrixMap.CPLe (Complex.ofReal s•P) (Complex.ofReal s•Q) := by
  have hh := MatrixMap.completelyPositive_smul hs h
  simpa only [smul_sub] using hh

theorem cpLe_divide {P Q : MatrixMap a b} {s : ℝ} (hs : 0<s)
    (h : MatrixMap.CPLe (Complex.ofReal s•P) Q) :
    MatrixMap.CPLe P (Complex.ofReal s⁻¹•Q) := by
  have hh := cpLe_smul h (inv_nonneg.mpr hs.le)
  simpa only [smul_smul,← Complex.ofReal_mul,inv_mul_cancel₀ hs.ne',Complex.ofReal_one,one_smul] using hh

/-- The actual normalized completion, with no assumed channel or norm oracle. -/
theorem complete_close_branch (F : Set (MatrixMap a b)) (hF : Convex ℝ (MatrixMap.choi '' F))
    (J Z : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (M : KrausChannel a b) (hM : M.toLinearMap∈F) (ω : State b)
    (hR : (ReplacerChannel.channel a ω).toLinearMap∈F)
    (c δ : ℝ) (hc : 1≤c) (hδ : 0≤δ)
    (hdom : MatrixMap.CPLe (adMap Z) (Complex.ofReal c•M.toLinearMap))
    (hclose : ‖Z-J‖≤δ) :
    ∃ L S : KrausChannel a b, S.toLinearMap∈F ∧
      MatrixMap.CPLe L.toLinearMap (Complex.ofReal (c+1)•S.toLinearMap) ∧
      DiamondNorm.diamondNorm (L.toLinearMap-adMap J)≤ENNReal.ofReal (8*δ) := by
  have hWM : dilationMap M.stinespring=M.toLinearMap := by
    apply LinearMap.ext
    intro X
    exact (dilationMap_apply M.stinespring X).trans (M.traceEnvironment_stinespring X)
  obtain ⟨A,hA,hAZ⟩ := UniformAuxiliary.lemma_6_exact (lift Z) M.stinespring c (by linarith)
    (by simpa only [dilationMap_lift,hWM] using hdom)
  have hAJ : ‖lift J-EnvironmentTensor.applyEnvironment M.stinespring A‖≤δ := by
    have he : EnvironmentTensor.applyEnvironment M.stinespring A=lift Z := (sub_eq_zero.mp hAZ).symm
    rw [he]
    have hd : lift J-lift Z=lift (J-Z) := rfl
    rw [hd,norm_lift,norm_sub_rev]
    exact hclose
  obtain ⟨L,S,hS,hD,hE⟩ := FreeAmplification.complete_auxiliary F hF
    (BranchExtraction.isometryChannel J hJ) M ha ω hM hR (lift J) M.stinespring
    (by exact ChannelDilationPower.reindex_isometry _ _ _ hJ)
    (by rw [dilationMap_lift,isometryChannel_map]) hWM A c δ hc hδ
    (by nlinarith [norm_nonneg A,Real.sqrt_nonneg c,Real.sq_sqrt (show 0≤c by linarith)]) hAJ
  exact ⟨L,S,hS,hD,by simpa only [isometryChannel_map] using hE⟩

/-- The coefficient p survives normalization except for the exact factor 2H². -/
theorem complete_weighted_branch (F : Set (MatrixMap a b)) (hF : Convex ℝ (MatrixMap.choi '' F))
    (J Z : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (M : KrausChannel a b) (hM : M.toLinearMap∈F) (ω : State b)
    (hR : (ReplacerChannel.channel a ω).toLinearMap∈F)
    (p H δ : ℝ) (hp : 0<p) (hp1 : p≤1) (hH : 1≤H) (hδ : 0≤δ)
    (hdom : MatrixMap.CPLe (Complex.ofReal (p/H^2)•adMap Z) M.toLinearMap)
    (hclose : ‖Z-J‖≤δ) :
    ∃ L S : KrausChannel a b, S.toLinearMap∈F ∧
      MatrixMap.CPLe (Complex.ofReal (p/(2*H^2))•L.toLinearMap) S.toLinearMap ∧
      DiamondNorm.diamondNorm (L.toLinearMap-adMap J)≤ENNReal.ofReal (8*δ) := by
  have hH0 : 0<H := by linarith
  have hc : 1≤H^2/p := (le_div_iff₀ hp).mpr (by nlinarith)
  have hD : MatrixMap.CPLe (adMap Z) (Complex.ofReal (H^2/p)•M.toLinearMap) := by
    simpa only [inv_div] using cpLe_divide (div_pos hp (sq_pos_of_pos hH0)) hdom
  obtain ⟨L,S,hS,hLS,herr⟩ := complete_close_branch F hF J Z hJ ha M hM ω hR (H^2/p) δ hc hδ hD hclose
  have hLS' := FreeAmplification.cpLe_scalar_mono L.toLinearMap S (show H^2/p+1≤2*H^2/p by calc
    _ ≤ 2*(H^2/p) := by linarith
    _ = _ := by ring) hLS
  have hscale := cpLe_smul hLS' (show 0≤p/(2*H^2) by positivity)
  have he : (p/(2*H^2))*(2*H^2/p)=1 := by field_simp
  refine ⟨L,S,hS,?_,herr⟩
  simpa only [smul_smul,← Complex.ofReal_mul,he,Complex.ofReal_one,one_smul] using hscale

end GeneralizedChannelStein.CloseBranchCompletion
