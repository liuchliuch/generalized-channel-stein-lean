import GeneralizedChannelStein.InvariantIntegral
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # The genuine finite-dimensional Haar coefficient Gram operator -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace GeneralizedChannelStein.InvariantIntegral
open QuantumChannelStein Matrix TensorPower TensorPermutation MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Literal complex span of the actual unitary tensor powers. -/
def unitarySpan (d n : ℕ) : Submodule ℂ (TensorOperator d n) :=
  Submodule.span ℂ (Set.range (fun U : UnitaryGroup d => (tensorUnitary d n U).val))

/-- Actual matrix coefficient against the tensor representation. -/
def coefficient (d n : ℕ) (X : TensorOperator d n) (U : UnitaryGroup d) : ℂ :=
  ((tensorUnitary d n U).valᴴ * X).trace

theorem continuous_coefficient (d n : ℕ) (X : TensorOperator d n) :
    Continuous (coefficient d n X) := by
  have h := continuous_tensorUnitary_val d n
  unfold coefficient Matrix.trace Matrix.diag
  fun_prop

@[simp] theorem coefficient_add (d n : ℕ) (X Y : TensorOperator d n) (U : UnitaryGroup d) :
    coefficient d n (X+Y) U = coefficient d n X U + coefficient d n Y U := by
  simp [coefficient, Matrix.mul_add, Matrix.trace_add]

@[simp] theorem coefficient_smul (d n : ℕ) (c : ℂ) (X : TensorOperator d n) (U : UnitaryGroup d) :
    coefficient d n (c • X) U = c * coefficient d n X U := by
  simp [coefficient, Matrix.mul_smul, Matrix.trace_smul]

/-- The actual Haar frame operator, defined on all ambient matrices. -/
def gram (d n : ℕ) (X : TensorOperator d n) : TensorOperator d n :=
  weightedIntegral d n (coefficient d n X)

theorem gram_add (d n : ℕ) (X Y : TensorOperator d n) : gram d n (X+Y) = gram d n X+gram d n Y := by
  simp only [gram, weightedIntegral, coefficient_add, add_smul]
  exact integral_add (integrable_weighted d n _ (continuous_coefficient d n X))
    (integrable_weighted d n _ (continuous_coefficient d n Y))

theorem gram_smul (d n : ℕ) (c : ℂ) (X : TensorOperator d n) : gram d n (c • X) = c • gram d n X := by
  simp only [gram, weightedIntegral, coefficient_smul, SemigroupAction.mul_smul, integral_smul]

def gramLinearMap (d n : ℕ) : TensorOperator d n →ₗ[ℂ] TensorOperator d n where
  toFun := gram d n
  map_add' := gram_add d n
  map_smul' := gram_smul d n

/-- Every actual frame value belongs to the actual unitary span. -/
theorem gram_mem_span (d n : ℕ) (X : TensorOperator d n) : gram d n X ∈ unitarySpan d n := by
  apply ((unitarySpan d n).restrictScalars ℝ).convex.integral_mem
    (unitarySpan d n).closed_of_finiteDimensional
  · exact Filter.Eventually.of_forall fun U => (unitarySpan d n).smul_mem _
      (Submodule.subset_span ⟨U,rfl⟩)
  · exact integrable_weighted d n _ (continuous_coefficient d n X)

/-- The finite-dimensional frame operator with its true invariant domain. -/
def gramOnSpan (d n : ℕ) : unitarySpan d n →ₗ[ℂ] unitarySpan d n where
  toFun X := ⟨gram d n X.val,gram_mem_span d n X.val⟩
  map_add' X Y := by apply Subtype.ext; exact gram_add d n X.val Y.val
  map_smul' c X := by apply Subtype.ext; exact gram_smul d n c X.val

def tracePairing (d n : ℕ) (X : TensorOperator d n) : TensorOperator d n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun Y => (X*Y).trace
    map_add' := by intro Y Z; simp [Matrix.mul_add,Matrix.trace_add]
    map_smul' := by intro c Y; simp [Matrix.mul_smul,Matrix.trace_smul] }

/-- The actual Haar Gram quadratic form is the integral of squared coefficient magnitude. -/
theorem trace_gram_quadratic (d n : ℕ) (X : TensorOperator d n) :
    (Xᴴ * gram d n X).trace.re =
      ∫ U, Complex.normSq (coefficient d n X U) ∂haar d := by
  have h := (tracePairing d n Xᴴ).integral_comp_comm
    (integrable_weighted d n _ (continuous_coefficient d n X))
  have hpoint (U : UnitaryGroup d) :
      (Xᴴ * (coefficient d n X U • (tensorUnitary d n U).val)).trace =
        (Complex.normSq (coefficient d n X U) : ℂ) := by
    have hs : (Xᴴ * (tensorUnitary d n U).val).trace = star (coefficient d n X U) := by
      simpa only [coefficient, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        using (Matrix.trace_conjTranspose ((tensorUnitary d n U).valᴴ * X))
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hs, Complex.star_def, Complex.mul_conj]
  have hc : (Xᴴ * gram d n X).trace =
      Complex.ofReal (∫ U, Complex.normSq (coefficient d n X U) ∂haar d) := by
    change (tracePairing d n Xᴴ) (weightedIntegral d n (coefficient d n X)) = _
    rw [weightedIntegral, ← h]
    change (∫ U, (Xᴴ * (coefficient d n X U • (tensorUnitary d n U).val)).trace ∂haar d) = _
    simp_rw [hpoint]
    exact integral_ofReal
  simpa only [Complex.ofReal_re] using congrArg Complex.re hc

theorem gram_quadratic_nonneg (d n : ℕ) (X : TensorOperator d n) :
    0 ≤ (Xᴴ * gram d n X).trace.re := by
  rw [trace_gram_quadratic]
  exact integral_nonneg (fun U => Complex.normSq_nonneg _)

/-- Full support of genuine Haar measure makes a zero Gram value annihilate
every actual matrix coefficient, not merely almost every coefficient. -/
theorem coefficient_eq_zero_of_gram_zero (d n : ℕ) (X : TensorOperator d n)
    (hX : gram d n X = 0) : ∀ U, coefficient d n X U = 0 := by
  have hzero : (∫ U, Complex.normSq (coefficient d n X U) ∂haar d) = 0 := by
    rw [← trace_gram_quadratic, hX]
    simp
  have hcont : Continuous (fun U => Complex.normSq (coefficient d n X U)) :=
    Complex.continuous_normSq.comp (continuous_coefficient d n X)
  have hi : Integrable (fun U => Complex.normSq (coefficient d n X U)) (haar d) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun U => Complex.normSq_nonneg _) hi).mp hzero
  have hfun := MeasureTheory.Measure.eq_of_ae_eq hae hcont continuous_const
  intro U
  exact Complex.normSq_eq_zero.mp (congrFun hfun U)

/-- A frame value can vanish on its true span only at the zero matrix. -/
theorem eq_zero_of_mem_span_of_gram_zero (d n : ℕ) (X : TensorOperator d n)
    (hmem : X ∈ unitarySpan d n) (hX : gram d n X=0) : X=0 := by
  have hcoeff := coefficient_eq_zero_of_gram_zero d n X hX
  have hpair : ∀ Y ∈ unitarySpan d n, (Yᴴ*X).trace=0 := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem Y hY => obtain ⟨U,rfl⟩ := hY; exact hcoeff U
    | zero => simp
    | add Y Z hY hZ ihY ihZ => simp [Matrix.conjTranspose_add,Matrix.add_mul,Matrix.trace_add,ihY,ihZ]
    | smul c Y hY ih => simp [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.trace_smul,ih]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (hpair X hmem)

theorem gramOnSpan_injective (d n : ℕ) : Function.Injective (gramOnSpan d n) := by
  intro X Y hXY
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_mem_span_of_gram_zero d n (X.val-Y.val)
    ((unitarySpan d n).sub_mem X.property Y.property)
  change gramLinearMap d n (X.val-Y.val)=0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hXY)

/-- An actual, proved inverse of the Haar frame operator. -/
def gramEquiv (d n : ℕ) : unitarySpan d n ≃ₗ[ℂ] unitarySpan d n :=
  LinearEquiv.ofInjectiveEndo (gramOnSpan d n) (gramOnSpan_injective d n)

/-- Exact reconstruction on the actual unitary span with a continuous scalar density.
The quantitative dimension bound is a further result, not assumed here. -/
theorem exists_continuous_reconstruction (d n : ℕ) (W : TensorOperator d n)
    (hW : W ∈ unitarySpan d n) :
    ∃ f : UnitaryGroup d → ℂ, Continuous f ∧ weightedIntegral d n f = W := by
  let X := (gramEquiv d n).symm ⟨W,hW⟩
  refine ⟨coefficient d n X.val, continuous_coefficient d n X.val, ?_⟩
  exact congrArg Subtype.val ((gramEquiv d n).apply_symm_apply ⟨W,hW⟩)

end GeneralizedChannelStein.InvariantIntegral
