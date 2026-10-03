import QuantumChannelStein.ExponentialStinespring
import QuantumChannelStein.ParallelConverse
import QuantumChannelStein.Normalization

/-!
# Concrete dominated trace-nonincreasing subchannels

The map is completely positive on every finite reference and decreases the
trace of every positive input. The normalization and Choi domination below
use actual fixed-environment dilation matrices. Diamond estimates are separate.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

/-- A genuine CP, trace-nonincreasing finite-dimensional matrix map. -/
structure Subchannel (a b : ℕ) where
  toLinearMap : MatrixMap a b
  completelyPositive : MatrixMap.CompletelyPositive toLinearMap
  trace_nonincreasing : ∀ X : Operator a, X.PosSemidef →
    (toLinearMap X).trace.re ≤ X.trace.re

namespace DominatedSubchannels
variable {a b e eN eM : ℕ}

theorem trace_traceEnvironment (X : Matrix (Fin b × Fin e) (Fin b × Fin e) ℂ) :
    (KrausChannel.traceEnvironment X).trace = X.trace := by
  simp [KrausChannel.traceEnvironment, Matrix.trace, Fintype.sum_prod_type]

/-- Every contraction dilation defines a trace-nonincreasing CP map. -/
def subchannelOfDilation (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : ‖V‖ ≤ 1) :
    Subchannel a b where
  toLinearMap := dilationMap V
  completelyPositive := MatrixMap.completelyPositive_ofKraus _
  trace_nonincreasing := by
    intro X hX
    have hgram : (1 - Vᴴ * V).PosSemidef := by
      simpa only [Matrix.conjTranspose_conjTranspose] using
        gram_le_one_of_norm_le_one Vᴴ (by simpa only [Matrix.l2_opNorm_conjTranspose] using hV)
    have htr := (Complex.nonneg_iff.mp (trace_mul_nonnegative hX hgram)).1
    rw [dilationMap_apply, trace_traceEnvironment, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    simpa only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re,
      sub_nonneg] using htr

/-- The positive Gram matrix bound associated with the genuine Hilbert operator norm. -/
theorem gram_le_scalar_of_norm_sq_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (D : Matrix ι κ ℂ) {c : ℝ}
    (hc : 0 ≤ c) (hD : ‖D‖ ^ 2 ≤ c) : (c • (1 : Matrix ι ι ℂ) - D * Dᴴ).PosSemidef := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  have hp := posSemidef_self_mul_conjTranspose D
  apply Matrix.nonneg_iff_posSemidef.mp
  apply sub_nonneg.mpr
  have hn : ‖D * Dᴴ‖ ≤ c := by
    calc
      _ ≤ ‖D‖ * ‖Dᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖D‖ ^ 2 := by rw [Matrix.l2_opNorm_conjTranspose, pow_two]
      _ ≤ c := hD
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (CStarAlgebra.norm_le_iff_le_algebraMap (D * Dᴴ) hc hp.nonneg).mp hn

/-- A bounded environment operation gives an actual CP comparison. -/
theorem dilationMap_environment_cpLe
    (V : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (D : Matrix (Fin eN) (Fin eM) ℂ) {c : ℝ} (hc : 0 ≤ c) (hD : ‖D‖ ^ 2 ≤ c) :
    MatrixMap.CPLe (dilationMap (((1 : Operator b) ⊗ₖ D) * V))
      ((c : ℂ) • dilationMap V) := by
  rw [MatrixMap.cpLe_iff_choi_difference, MatrixMap.choi_smul,
    choi_dilationMap, choi_dilationMap, dilationColumns_environment]
  have hgram := gram_le_scalar_of_norm_sq_le Dᵀ hc
    (by simpa only [TransposeNorm.opNorm_transpose] using hD)
  have h := hgram.mul_mul_conjTranspose_same (dilationColumns V)
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.conjTranspose_mul, Matrix.mul_assoc, Complex.real_smul] using h

/-- Scaling down by one plus a nonnegative error never increases auxiliary cost. -/
theorem norm_normalize_le (C : Matrix (Fin eN) (Fin eM) ℂ) {error : ℝ}
    (he : 0 ≤ error) : ‖Normalization.normalize error C‖ ≤ ‖C‖ := by
  have hden : 0 < 1 + error := by linarith
  have hi : (1 + error)⁻¹ ≤ 1 := (inv_le_one₀ hden).mpr (by linarith)
  rw [Normalization.normalize, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hden.le)]
  exact mul_le_of_le_one_left (norm_nonneg C) hi

/-- The normalized approximation retains the original environment spaces. -/
theorem normalize_environment
    (V : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (C : Matrix (Fin eN) (Fin eM) ℂ) (error : ℝ) :
    Normalization.normalize error (((1 : Operator b) ⊗ₖ C) * V) =
      ((1 : Operator b) ⊗ₖ Normalization.normalize error C) * V := by
  simp only [Normalization.normalize, Matrix.kronecker_smul, Matrix.smul_mul]

/-- The normalization step in Corollary 5.2, with its genuine subchannel,
CP domination, and the operator-dilation error bound. -/
theorem normalized_dominated_subchannel
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVN : VNᴴ * VN = 1) (C : Matrix (Fin eN) (Fin eM) ℂ)
    (error c : ℝ) (he : 0 ≤ error) (hc : 0 ≤ c)
    (hC : ‖C‖ ^ 2 ≤ c) (herr : ‖VN - ((1 : Operator b) ⊗ₖ C) * VM‖ ≤ error) :
    ∃ L : Subchannel a b, ∃ W : Matrix (Fin b × Fin eN) (Fin a) ℂ,
      W = Normalization.normalize error (((1 : Operator b) ⊗ₖ C) * VM) ∧
      L.toLinearMap = dilationMap W ∧ ‖W‖ ≤ 1 ∧
      MatrixMap.CPLe L.toLinearMap ((c : ℂ) • dilationMap VM) ∧
      ‖VN - W‖ ≤ 2 * error := by
  let W := Normalization.normalize error (((1 : Operator b) ⊗ₖ C) * VM)
  have hV := UniformApproximation.norm_isometry_le_one VN hVN
  have hW : ‖W‖ ≤ 1 := Normalization.norm_normalize_le_one he hV herr
  refine ⟨subchannelOfDilation W hW, W, rfl, rfl, hW, ?_,
    Normalization.norm_sub_normalize_le_double he hV herr⟩
  change MatrixMap.CPLe (dilationMap W) _
  dsimp [W]
  rw [normalize_environment]
  apply dilationMap_environment_cpLe VM _ hc
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_normalize_le C he) 2).trans hC

end DominatedSubchannels
end QuantumChannelStein
