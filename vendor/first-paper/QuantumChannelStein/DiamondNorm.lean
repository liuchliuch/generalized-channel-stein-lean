import QuantumChannelStein.TraceNormBounds
import QuantumChannelStein.DominatedSubchannels

/-!
# The unhalved completely bounded trace norm of genuine matrix maps

The definition optimizes the standard trace-square-root norm over every finite
reference and every input matrix in its unit ball. It is the full, unhalved
diamond norm, not a restricted state-test distance. The dilation comparison
is proved directly for all such matrices, so no pure-state reduction or
trace-norm-contraction assumption is needed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.DiamondNorm
open Matrix TraceNorm ReferenceAcceptance
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
variable {a b e : ℕ}

/-- Unhalved completely bounded trace norm, in extended nonnegative reals.
All finite references and all trace-norm-unit-ball matrices are included. -/
def diamondNorm (Φ : MatrixMap a b) : ENNReal :=
  ⨆ r : ℕ, ⨆ X : {X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ // traceNorm X ≤ 1},
    ENNReal.ofReal (traceNorm (MatrixMap.amplify Φ r X.val))

/-- Exact amplification semantics for an arbitrary, possibly nonisometric dilation. -/
theorem amplify_dilationMap
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (r : ℕ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    MatrixMap.amplify (dilationMap V) r X =
      traceEnvironment (dilation (r := Fin r) V * X * (dilation (r := Fin r) V)ᴴ) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [MatrixMap.amplify, dilationMap, MatrixMap.ofKraus, Matrix.sum_apply,
    traceEnvironment, dilation, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

/-- The amplified difference is the actual partial trace of the two
conjugation outputs, with the canonical reference/output reassociation. -/
theorem amplify_dilationMap_sub
    (V W : Matrix (Fin b × Fin e) (Fin a) ℂ) (r : ℕ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    MatrixMap.amplify (dilationMap V - dilationMap W) r X =
      traceEnvironment (dilation (r := Fin r) V * X * (dilation (r := Fin r) V)ᴴ - dilation (r := Fin r) W * X * (dilation (r := Fin r) W)ᴴ) := by
  have hsub : MatrixMap.amplify (dilationMap V - dilationMap W) r X =
      MatrixMap.amplify (dilationMap V) r X - MatrixMap.amplify (dilationMap W) r X := rfl
  rw [hsub, amplify_dilationMap, amplify_dilationMap]
  ext i j
  simp [traceEnvironment, Finset.sum_sub_distrib]

/-- Uniform all-reference trace-norm estimate for two contraction dilations. -/
theorem amplify_dilation_difference_le
    (V W : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    (r : ℕ) (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    traceNorm (MatrixMap.amplify (dilationMap V - dilationMap W) r X) ≤
      2 * ‖V - W‖ * traceNorm X := by
  rw [amplify_dilationMap_sub]
  have hv : ‖dilation (r := Fin r) V‖ ≤ 1 := (dilation_opNorm_le V).trans hV
  have hw : ‖dilation (r := Fin r) W‖ ≤ 1 := (dilation_opNorm_le W).trans hW
  have hd : ‖dilation (r := Fin r) V - dilation (r := Fin r) W‖ ≤ ‖V - W‖ := by
    rw [← dilation_sub]
    exact dilation_opNorm_le _
  calc
    _ ≤ traceNorm (dilation (r := Fin r) V * X * (dilation (r := Fin r) V)ᴴ - dilation (r := Fin r) W * X * (dilation (r := Fin r) W)ᴴ) :=
      traceNorm_partialTrace_le _
    _ ≤ (‖dilation (r := Fin r) V‖ + ‖dilation (r := Fin r) W‖) *
        ‖dilation (r := Fin r) V - dilation (r := Fin r) W‖ * traceNorm X := traceNorm_dilation_difference_le _ _ _
    _ ≤ 2 * ‖V - W‖ * traceNorm X := by
      have hs : ‖dilation (r := Fin r) V‖ + ‖dilation (r := Fin r) W‖ ≤ 2 := by linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hs hd (norm_nonneg _) (by norm_num)) (traceNorm_nonneg X)

/-- Actual unhalved diamond distance is at most twice the dilation error. -/
theorem diamondNorm_dilation_difference_le
    (V W : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    diamondNorm (dilationMap V - dilationMap W) ≤ ENNReal.ofReal (2 * ‖V - W‖) := by
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  apply ENNReal.ofReal_le_ofReal
  exact (amplify_dilation_difference_le V W hV hW r X.val).trans
    (mul_le_of_le_one_right (by positivity) X.property)

/-- In particular this genuine diamond distance is finite. -/
theorem diamondNorm_dilation_difference_ne_top
    (V W : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    diamondNorm (dilationMap V - dilationMap W) ≠ ⊤ :=
  ne_of_lt ((diamondNorm_dilation_difference_le V W hV hW).trans_lt ENNReal.ofReal_lt_top)

end QuantumChannelStein.DiamondNorm
