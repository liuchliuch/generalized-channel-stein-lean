import QuantumChannelStein.MaxRelativeEntropy

/-! # Actual testing consequences of diamond closeness and CP domination -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.DiamondTesting
open Matrix TraceNorm DiamondNorm ChannelEntropy TestingPrimal OperationalTesting
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- The actual reference-assisted Born weight for an arbitrary linear map. -/
def testValue (L : MatrixMap a b) (ψ : UnitPureInput a a) (T : Effect (a * b)) : ℝ :=
  (rawEffect T * MatrixMap.amplify L a (pureMatrix ψ.val)).trace.re

/-- For channels, this is exactly the original operational acceptance probability. -/
theorem testValue_channel (Φ : KrausChannel a b) (ψ : UnitPureInput a a)
    (T : Effect (a * b)) : testValue Φ.toLinearMap ψ T = T.probability (pureOutput Φ ψ) := by
  rw [testValue, MatrixMap.amplify_toLinearMap]
  exact (pureOutput_probability_raw Φ ψ T).symm

theorem testValue_sub (L M : MatrixMap a b) (ψ : UnitPureInput a a) (T : Effect (a * b)) :
    testValue (L - M) ψ T = testValue L ψ T - testValue M ψ T := by
  have h : MatrixMap.amplify (L - M) a (pureMatrix ψ.val) =
      MatrixMap.amplify L a (pureMatrix ψ.val) - MatrixMap.amplify M a (pureMatrix ψ.val) := rfl
  simp only [testValue, h, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

/-- CP domination bounds the actual pure-input test weight even for subchannels. -/
theorem testValue_le_of_cpLe (L : MatrixMap a b) (Ψ : KrausChannel a b) (t : ℝ)
    (h : MatrixMap.CPLe L ((t : ℂ) • Ψ.toLinearMap))
    (ψ : UnitPureInput a a) (T : Effect (a * b)) :
    testValue L ψ T ≤ t * T.probability (pureOutput Ψ ψ) := by
  have hp := h a (pureMatrix ψ.val) (pureMatrix_positive ψ.val)
  have hmat : MatrixMap.amplify ((t : ℂ) • Ψ.toLinearMap - L) a (pureMatrix ψ.val) =
      (t : ℂ) • MatrixMap.amplify Ψ.toLinearMap a (pureMatrix ψ.val) -
        MatrixMap.amplify L a (pureMatrix ψ.val) := rfl
  rw [hmat] at hp
  have ht := (Complex.nonneg_iff.mp
    (TestingSDP.trace_pairing_nonnegative (rawEffect_positive T) hp)).1
  rw [← testValue_channel Ψ ψ T]
  simpa only [testValue, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, sub_nonneg] using ht

/-- Diamond closeness preserves every actual pure-test acceptance up to its radius. -/
theorem probability_sub_radius_le_testValue (Φ : KrausChannel a b) (L : MatrixMap a b)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hclose : diamondNorm (L - Φ.toLinearMap) ≤ ENNReal.ofReal ε)
    (ψ : UnitPureInput a a) (T : Effect (a * b)) :
    T.probability (pureOutput Φ ψ) - ε ≤ testValue L ψ T := by
  let X := pureMatrix ψ.val
  have hX : traceNorm X = 1 := by
    rw [traceNorm_of_posSemidef X (pureMatrix_positive ψ.val),
      trace_pureMatrix_of_norm_one ψ.val ψ.property]
    rfl
  have hY : ENNReal.ofReal (traceNorm (MatrixMap.amplify (L - Φ.toLinearMap) a X)) ≤
      diamondNorm (L - Φ.toLinearMap) := le_iSup_of_le a (le_iSup_of_le ⟨X, hX.le⟩ le_rfl)
  have hYn : traceNorm (MatrixMap.amplify (L - Φ.toLinearMap) a X) ≤ ε :=
    (ENNReal.ofReal_le_ofReal_iff hε).mp (hY.trans hclose)
  have hT : ‖rawEffect T‖ ≤ 1 := by
    rw [rawEffect, TensorPower.norm_reindex]
    exact T.norm_matrix_le_one
  have hpair := (norm_trace_mul_le (rawEffect T)
    (MatrixMap.amplify (L - Φ.toLinearMap) a X)).trans
      (mul_le_of_le_one_left (traceNorm_nonneg _) hT)
  have hweight : -testValue (L - Φ.toLinearMap) ψ T ≤ ε :=
    ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (hpair.trans hYn)
  rw [testValue_sub, testValue_channel] at hweight
  linarith

/-- The key one-shot operational implication in the proof of Corollary 5.3. -/
theorem probability_sub_radius_le_scaled_alternative
    (Φ Ψ : KrausChannel a b) (L : MatrixMap a b) (ε t : ℝ) (hε : 0 ≤ ε)
    (hclose : diamondNorm (L - Φ.toLinearMap) ≤ ENNReal.ofReal ε)
    (hdom : MatrixMap.CPLe L ((t : ℂ) • Ψ.toLinearMap))
    (ψ : UnitPureInput a a) (T : Effect (a * b)) :
    T.probability (pureOutput Φ ψ) - ε ≤ t * T.probability (pureOutput Ψ ψ) :=
  (probability_sub_radius_le_testValue Φ L ε hε hclose ψ T).trans
    (testValue_le_of_cpLe L Ψ t hdom ψ T)

/-- The literal operational beta infimum inherits the scalar lower bound
from every actual diamond-feasible, CP-dominated approximating map. -/
theorem parallelPureBeta_lower_of_diamond_cp
    (Φ Ψ : KrausChannel a b) (k : ℕ)
    (L : MatrixMap (a ^ k) (b ^ k)) (ε η t : ℝ) (hε : 0 ≤ ε) (ht : 0 < t)
    (hclose : diamondNorm (L - (Φ.tensorPower k).toLinearMap) ≤ ENNReal.ofReal ε)
    (hdom : MatrixMap.CPLe L ((t : ℂ) • (Ψ.tensorPower k).toLinearMap)) :
    ENNReal.ofReal ((1 - η - ε) / t) ≤ parallelPureBeta Φ Ψ k η := by
  apply le_iInf
  intro test
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ ht).mpr
  have hp := probability_sub_radius_le_scaled_alternative (Φ.tensorPower k) (Ψ.tensorPower k)
    L ε t hε hclose hdom test.val.1 test.val.2
  linarith [test.property]

end QuantumChannelStein.DiamondTesting
