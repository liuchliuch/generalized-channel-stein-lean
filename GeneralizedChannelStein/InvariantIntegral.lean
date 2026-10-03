import QuantumChannelStein.InvariantSpectralBound
import QuantumChannelStein.TraceNorm
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Actual Haar integrals of unitary tensor powers

This module builds the concrete compact group, normalized Haar measure,
and actual tensor representation. Reconstruction of every permutation
invariant contraction is a further theorem, not an assumed interface.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.InvariantIntegral
open QuantumChannelStein Matrix TensorPower TensorPermutation MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

abbrev UnitaryGroup (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ
abbrev TensorOperator (d n : ℕ) := Matrix (Index (Fin d) n) (Index (Fin d) n) ℂ

instance unitaryCompact (d : ℕ) : CompactSpace (UnitaryGroup d) := by
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
  apply isBounded_iff_forall_norm_le.mpr
  exact ⟨1, fun U hU => TraceNorm.unitary_opNorm_le_one ⟨U,hU⟩⟩

instance unitaryMeasurableSpace (d : ℕ) : MeasurableSpace (UnitaryGroup d) := borel _
instance unitaryBorelSpace (d : ℕ) : BorelSpace (UnitaryGroup d) := ⟨rfl⟩

def unitaryPositiveCompact (d : ℕ) : TopologicalSpace.PositiveCompacts (UnitaryGroup d) :=
  ⟨⟨Set.univ,isCompact_univ⟩, by simp⟩

/-- Genuine Haar probability on the actual finite-dimensional unitary group. -/
def haar (d : ℕ) : Measure (UnitaryGroup d) := Measure.haarMeasure (unitaryPositiveCompact d)

instance haar_isHaarMeasure (d : ℕ) : Measure.IsHaarMeasure (haar d) := by
  unfold haar
  infer_instance

instance haar_isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (haar d) :=
  ⟨by exact Measure.haarMeasure_self⟩

/-- Actual independent tensoring gives a group representation by unitary matrices. -/
def tensorUnitary (d n : ℕ) (U : UnitaryGroup d) :
    Matrix.unitaryGroup (Index (Fin d) n) ℂ :=
  ⟨tensorPower U.val n, Matrix.mem_unitaryGroup_iff'.mpr
    (tensorPower_isometry U.val (Unitary.coe_star_mul_self U) n)⟩

def tensorRepresentation (d n : ℕ) : UnitaryGroup d →* Matrix.unitaryGroup (Index (Fin d) n) ℂ where
  toFun := tensorUnitary d n
  map_one' := by apply Subtype.ext; exact tensorPower_one n
  map_mul' U V := by apply Subtype.ext; exact tensorPower_mul U.val V.val n

theorem continuous_tensorPower (d n : ℕ) :
    Continuous (fun A : Operator d => tensorPower A n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [tensorPower_apply_eq_prod]
  fun_prop

theorem continuous_tensorUnitary_val (d n : ℕ) :
    Continuous (fun U : UnitaryGroup d => (tensorUnitary d n U).val) :=
  (continuous_tensorPower d n).comp continuous_subtype_val

theorem norm_tensorUnitary_le (d n : ℕ) (U : UnitaryGroup d) :
    ‖(tensorUnitary d n U).val‖ ≤ 1 := TraceNorm.unitary_opNorm_le_one _

theorem tensorUnitary_invariant (d n : ℕ) (U : UnitaryGroup d) :
    (tensorUnitary d n U).val ∈ invariantAlgebra (Fin d) n :=
  tensorPower_mem_invariantAlgebra U.val n

/-- The literal complex linear Haar integral, not a probability mixture. -/
def weightedIntegral (d n : ℕ) (f : UnitaryGroup d → ℂ) : TensorOperator d n :=
  ∫ U, f U • (tensorUnitary d n U).val ∂haar d

theorem integrable_weighted (d n : ℕ) (f : UnitaryGroup d → ℂ) (hf : Continuous f) :
    Integrable (fun U => f U • (tensorUnitary d n U).val) (haar d) :=
  (hf.smul (continuous_tensorUnitary_val d n)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The actual integral is bounded by a uniform absolute coefficient bound. -/
theorem norm_weightedIntegral_le (d n : ℕ) (f : UnitaryGroup d → ℂ) (_hf : Continuous f)
    (B : ℝ) (hB : ∀ U, ‖f U‖ ≤ B) : ‖weightedIntegral d n f‖ ≤ B := by
  have hpoint (U : UnitaryGroup d) : ‖f U • (tensorUnitary d n U).val‖ ≤ B := by
    rw [norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_tensorUnitary_le d n U)).trans (hB U)
  have h := norm_integral_le_of_norm_le_const (μ := haar d)
    (Filter.Eventually.of_forall hpoint)
  simpa only [weightedIntegral, probReal_univ, mul_one] using h

/-- Every weighted Haar integral is genuinely permutation invariant. -/
theorem weightedIntegral_invariant (d n : ℕ) (f : UnitaryGroup d → ℂ) (hf : Continuous f) :
    weightedIntegral d n f ∈ invariantAlgebra (Fin d) n := by
  intro p
  let L : TensorOperator d n →L[ℂ] TensorOperator d n :=
    (conjugation (Fin d) n p).toLinearMap.toContinuousLinearMap
  have h := L.integral_comp_comm (integrable_weighted d n f hf)
  change L (weightedIntegral d n f) = weightedIntegral d n f
  rw [weightedIntegral, ← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun U => by
    change conjugation (Fin d) n p (f U • (tensorUnitary d n U).val) = _
    rw [map_smul, (tensorUnitary_invariant d n U) p]

end GeneralizedChannelStein.InvariantIntegral
