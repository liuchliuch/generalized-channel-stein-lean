import QuantumChannelStein.DiamondNormChannel
import QuantumChannelStein.ChannelComposition

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.PostprocessingBounds
open QuantumChannelStein DiamondNorm
variable {a b c : ℕ}

/-- Exact amplification of composition for arbitrary complex-linear matrix maps. -/
theorem amplify_comp (P : MatrixMap b c) (Q : MatrixMap a b) (r : ℕ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    MatrixMap.amplify (P.comp Q) r X =
      MatrixMap.amplify P r (MatrixMap.amplify Q r X) := rfl

/-- CPTP postcomposition contracts the full diamond norm, on arbitrary maps. -/
theorem diamondNorm_postcompose (D : KrausChannel b c) (Q : MatrixMap a b) :
    diamondNorm (D.toLinearMap.comp Q) ≤ diamondNorm Q := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  rw [amplify_comp]
  exact (ENNReal.ofReal_le_ofReal (traceNorm_amplify_channel_le D r _)).trans
    (le_iSup_of_le r (le_iSup_of_le X le_rfl))

theorem compose_map (D : KrausChannel b c) (L : KrausChannel a b) :
    (D.compose L).toLinearMap = D.toLinearMap.comp L.toLinearMap := by
  ext X i j
  exact congrFun (congrFun (KrausChannel.compose_apply D L X) i) j

/-- Actual channel differences inherit full diamond-norm contractivity. -/
theorem diamondNorm_compose_sub (D : KrausChannel b c) (L N : KrausChannel a b) :
    diamondNorm ((D.compose L).toLinearMap-(D.compose N).toLinearMap) ≤
      diamondNorm (L.toLinearMap-N.toLinearMap) := by
  rw [compose_map,compose_map,← LinearMap.comp_sub]
  exact diamondNorm_postcompose D _

/-- CP order is preserved by any completely positive postprocessing map. -/
theorem cpLe_postcompose {P : MatrixMap b c} (hP : MatrixMap.CompletelyPositive P)
    {Q Q' : MatrixMap a b} (hQ : MatrixMap.CPLe Q Q') :
    MatrixMap.CPLe (P.comp Q) (P.comp Q') := by
  change MatrixMap.CompletelyPositive (P.comp Q'-P.comp Q)
  rw [← LinearMap.comp_sub]
  intro r X hX
  rw [amplify_comp]
  exact hP r _ (hQ r X hX)

/-- Scalar CP domination, with the scalar exactly preserved by actual postcomposition. -/
theorem cpLe_compose_scalar (D : KrausChannel b c) (L S : KrausChannel a b)
    (z : ℂ) (h : MatrixMap.CPLe (z • L.toLinearMap) S.toLinearMap) :
    MatrixMap.CPLe (z • (D.compose L).toLinearMap) (D.compose S).toLinearMap := by
  have hp := cpLe_postcompose (MatrixMap.completelyPositive_toLinearMap D) h
  simpa only [compose_map,LinearMap.comp_smul] using hp

/-- The alternative scaling convention is preserved as well. -/
theorem cpLe_scalar_compose (D : KrausChannel b c) (L S : KrausChannel a b)
    (z : ℂ) (h : MatrixMap.CPLe L.toLinearMap (z • S.toLinearMap)) :
    MatrixMap.CPLe (D.compose L).toLinearMap (z • (D.compose S).toLinearMap) := by
  have hp := cpLe_postcompose (MatrixMap.completelyPositive_toLinearMap D) h
  simpa only [compose_map,LinearMap.comp_smul] using hp

/-- A concrete output reduction transfers membership, domination, and approximation together. -/
theorem postprocess_approximation (D : KrausChannel b c) (L N S : KrausChannel a b)
    (N₀ : KrausChannel a c) (F : Set (MatrixMap a c)) (z : ℂ) (ε : ENNReal)
    (hN : (D.compose N).toLinearMap = N₀.toLinearMap)
    (hS : D.toLinearMap.comp S.toLinearMap ∈ F)
    (hdom : MatrixMap.CPLe (z • L.toLinearMap) S.toLinearMap)
    (hclose : diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ε) :
    ∃ L' S' : KrausChannel a c, S'.toLinearMap ∈ F ∧
      MatrixMap.CPLe (z • L'.toLinearMap) S'.toLinearMap ∧
      diamondNorm (L'.toLinearMap-N₀.toLinearMap) ≤ ε := by
  refine ⟨D.compose L,D.compose S,?_,cpLe_compose_scalar D L S z hdom,?_⟩
  · rwa [compose_map]
  · rw [← hN]
    exact (diamondNorm_compose_sub D L N).trans hclose

end GeneralizedChannelStein.PostprocessingBounds
