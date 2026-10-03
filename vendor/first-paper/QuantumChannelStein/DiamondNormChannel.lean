import QuantumChannelStein.DiamondNorm

/-! # Channel diamond normalization and exclusion of the zero approximant -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein
open Matrix TraceNorm ReferenceAcceptance ChannelEntropy ParallelConverse
open scoped BigOperators Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TraceNorm
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard trace norm agrees with the real trace on positive matrices. -/
theorem traceNorm_of_posSemidef (X : Matrix ι ι ℂ) (hX : X.PosSemidef) :
    traceNorm X = X.trace.re := by
  rw [traceNorm, hX.isHermitian.eq, ← pow_two, CFC.sqrt_sq X hX.nonneg]

@[simp] theorem traceNorm_neg (X : Matrix ι ι ℂ) : traceNorm (-X) = traceNorm X := by
  simp [traceNorm]

end TraceNorm

namespace DiamondNorm
variable {a b : ℕ}

@[simp] theorem diamondNorm_neg (Φ : MatrixMap a b) : diamondNorm (-Φ) = diamondNorm Φ := by
  unfold diamondNorm
  congr 1
  ext r
  congr 1
  ext X
  have h : MatrixMap.amplify (-Φ) r X.val = -MatrixMap.amplify Φ r X.val := rfl
  rw [h, traceNorm_neg]

/-- The actual amplified channel contracts the standard trace norm, on all matrices. -/
theorem traceNorm_amplify_channel_le (Φ : KrausChannel a b) (r : ℕ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    traceNorm (MatrixMap.amplify Φ.toLinearMap r X) ≤ traceNorm X := by
  rw [← dilationMap_stinespring Φ, amplify_dilationMap]
  have hv : ‖dilation (r := Fin r) Φ.stinespring‖ ≤ 1 :=
    (dilation_opNorm_le _).trans
      (UniformApproximation.norm_isometry_le_one _ Φ.stinespring_isometry)
  apply (traceNorm_partialTrace_le _).trans
  apply (traceNorm_sandwich_le _ _ _).trans
  rw [Matrix.l2_opNorm_conjTranspose]
  have hx := traceNorm_nonneg X
  calc
    _ ≤ 1 * traceNorm X * 1 := by gcongr
    _ = traceNorm X := by ring

/-- A trace-preserving channel has the genuine unhalved diamond norm one. -/
theorem diamondNorm_channel (Φ : KrausChannel a b) (ha : 0 < a) :
    diamondNorm Φ.toLinearMap = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro X
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      ((traceNorm_amplify_channel_le Φ r X.val).trans X.property)
  · let ψ := maximallyEntangledInput ha
    let X := pureMatrix ψ.val
    have hX : traceNorm X = 1 := by
      rw [traceNorm_of_posSemidef X (pureMatrix_positive ψ.val),
        trace_pureMatrix_of_norm_one ψ.val ψ.property]
      rfl
    have hY : traceNorm (MatrixMap.amplify Φ.toLinearMap a X) = 1 := by
      rw [MatrixMap.amplify_toLinearMap,
        traceNorm_of_posSemidef _ (Φ.amplify_positive _ (pureMatrix_positive ψ.val)),
        Φ.trace_amplify, trace_pureMatrix_of_norm_one ψ.val ψ.property]
      rfl
    have hle : ENNReal.ofReal (traceNorm (MatrixMap.amplify Φ.toLinearMap a X)) ≤
        diamondNorm Φ.toLinearMap :=
      le_iSup_of_le a (le_iSup_of_le ⟨X, hX.le⟩ le_rfl)
    simpa only [hY, ENNReal.ofReal_one] using hle

/-- Diamond radius strictly less than one genuinely excludes the zero map. -/
theorem nonzero_of_diamond_close (Φ : KrausChannel a b) (ha : 0 < a)
    (L : MatrixMap a b) (ε : ℝ) (hε : ε < 1)
    (hclose : diamondNorm (L - Φ.toLinearMap) ≤ ENNReal.ofReal ε) : L ≠ 0 := by
  intro hL
  rw [hL, zero_sub, diamondNorm_neg, diamondNorm_channel Φ ha] at hclose
  exact (not_le_of_gt (ENNReal.ofReal_lt_one.mpr hε)) hclose

end DiamondNorm
end QuantumChannelStein
