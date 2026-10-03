import GeneralizedChannelStein.HaarGram

/-! # Algebraic equivariance of the actual Haar coefficient frame -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace GeneralizedChannelStein.InvariantIntegral
open QuantumChannelStein Matrix TensorPower TensorPermutation MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

instance haar_isMulRightInvariant (d : ℕ) : Measure.IsMulRightInvariant (haar d) where
  map_mul_right_eq_self U := by
    have h := Measure.haarMeasure_unique (Measure.map (fun V : UnitaryGroup d => V*U) (haar d))
      (unitaryPositiveCompact d)
    have hv : Measure.map (fun V : UnitaryGroup d => V*U) (haar d) (unitaryPositiveCompact d) = 1 := by
      change Measure.map (fun V : UnitaryGroup d => V*U) (haar d) Set.univ = 1
      rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
      simp
    rw [hv,one_smul] at h
    exact h

@[simp] theorem tensorUnitary_mul (d n : ℕ) (U V : UnitaryGroup d) :
    (tensorUnitary d n (U*V)).val=(tensorUnitary d n U).val*(tensorUnitary d n V).val :=
  congrArg Subtype.val ((tensorRepresentation d n).map_mul U V)

@[simp] theorem tensorUnitary_one (d n : ℕ) : (tensorUnitary d n 1).val=1 :=
  congrArg Subtype.val ((tensorRepresentation d n).map_one)

@[simp] theorem tensorUnitary_adjoint (d n : ℕ) (U : UnitaryGroup d) :
    (tensorUnitary d n U).valᴴ=(tensorUnitary d n U⁻¹).val :=
  congrArg Subtype.val (map_inv (tensorRepresentation d n) U).symm

theorem unitarySpan_one_mem (d n : ℕ) : (1 : TensorOperator d n) ∈ unitarySpan d n := by
  rw [← tensorUnitary_one d n]
  exact Submodule.subset_span ⟨1,rfl⟩

theorem unitarySpan_mul_mem (d n : ℕ) {X Y : TensorOperator d n}
    (hX : X ∈ unitarySpan d n) (hY : Y ∈ unitarySpan d n) : X*Y ∈ unitarySpan d n := by
  have hleft (U : UnitaryGroup d) : (tensorUnitary d n U).val*Y ∈ unitarySpan d n := by
    induction hY using Submodule.span_induction with
    | mem Y hY =>
      obtain ⟨V,rfl⟩ := hY
      rw [← tensorUnitary_mul]
      exact Submodule.subset_span ⟨U*V,rfl⟩
    | zero => simpa using (unitarySpan d n).zero_mem
    | add Y Z hY hZ ihY ihZ => simpa only [Matrix.mul_add] using (unitarySpan d n).add_mem ihY ihZ
    | smul c Y hY ih => simpa only [Matrix.mul_smul] using (unitarySpan d n).smul_mem c ih
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨U,rfl⟩ := hX; exact hleft U
  | zero => simpa using (unitarySpan d n).zero_mem
  | add X Z hX hZ ihX ihZ => simpa only [Matrix.add_mul] using (unitarySpan d n).add_mem ihX ihZ
  | smul c X hX ih => simpa only [Matrix.smul_mul] using (unitarySpan d n).smul_mem c ih

theorem unitarySpan_adjoint_mem (d n : ℕ) {X : TensorOperator d n}
    (hX : X ∈ unitarySpan d n) : Xᴴ ∈ unitarySpan d n := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨U,rfl⟩ := hX
    rw [tensorUnitary_adjoint]
    exact Submodule.subset_span ⟨U⁻¹,rfl⟩
  | zero => simpa using (unitarySpan d n).zero_mem
  | add X Y hX hY ihX ihY => simpa using (unitarySpan d n).add_mem ihX ihY
  | smul c X hX ih => simpa only [Matrix.conjTranspose_smul] using (unitarySpan d n).smul_mem (star c) ih

def mulLeftCLM (d n : ℕ) (X : TensorOperator d n) : TensorOperator d n →L[ℂ] TensorOperator d n :=
  LinearMap.toContinuousLinearMap (Algebra.lmul ℂ (TensorOperator d n) X)

def mulRightCLM (d n : ℕ) (X : TensorOperator d n) : TensorOperator d n →L[ℂ] TensorOperator d n :=
  LinearMap.toContinuousLinearMap {
    toFun := fun Y => Y*X
    map_add' := fun Y Z => Matrix.add_mul _ _ _
    map_smul' := fun c Y => Matrix.smul_mul _ _ _ }

/-- Left Haar invariance gives exact left equivariance of the genuine frame. -/
theorem gram_mul_tensorUnitary_left (d n : ℕ) (U : UnitaryGroup d) (X : TensorOperator d n) :
    gram d n ((tensorUnitary d n U).val*X)=(tensorUnitary d n U).val*gram d n X := by
  have hcoeff (V : UnitaryGroup d) :
      coefficient d n ((tensorUnitary d n U).val*X) (U*V)=coefficient d n X V := by
    unfold coefficient
    rw [tensorUnitary_mul,Matrix.conjTranspose_mul]
    have hu : (tensorUnitary d n U).valᴴ*(tensorUnitary d n U).val=1 :=
      Unitary.coe_star_mul_self _
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (tensorUnitary d n U).valᴴ,hu,Matrix.one_mul]
  have hpoint (V : UnitaryGroup d) :
      coefficient d n ((tensorUnitary d n U).val*X) (U*V) • (tensorUnitary d n (U*V)).val =
        (tensorUnitary d n U).val*(coefficient d n X V • (tensorUnitary d n V).val) := by
    rw [hcoeff,tensorUnitary_mul,Matrix.mul_smul]
  rw [gram,weightedIntegral,← integral_mul_left_eq_self
    (fun V => coefficient d n ((tensorUnitary d n U).val*X) V • (tensorUnitary d n V).val) U]
  simp_rw [hpoint]
  exact (mulLeftCLM d n (tensorUnitary d n U).val).integral_comp_comm
    (integrable_weighted d n _ (continuous_coefficient d n X))

/-- Compactness normalizes right Haar invariance and supplies right equivariance. -/
theorem gram_mul_tensorUnitary_right (d n : ℕ) (U : UnitaryGroup d) (X : TensorOperator d n) :
    gram d n (X*(tensorUnitary d n U).val)=gram d n X*(tensorUnitary d n U).val := by
  have hcoeff (V : UnitaryGroup d) :
      coefficient d n (X*(tensorUnitary d n U).val) (V*U)=coefficient d n X V := by
    unfold coefficient
    rw [tensorUnitary_mul,Matrix.conjTranspose_mul]
    rw [Matrix.trace_mul_cycle]
    have hu : (tensorUnitary d n U).val*(tensorUnitary d n U).valᴴ=1 :=
      Unitary.coe_mul_star_self _
    rw [Matrix.mul_assoc X,hu,Matrix.mul_one,Matrix.trace_mul_comm]
  have hpoint (V : UnitaryGroup d) :
      coefficient d n (X*(tensorUnitary d n U).val) (V*U) • (tensorUnitary d n (V*U)).val =
        (coefficient d n X V • (tensorUnitary d n V).val)*(tensorUnitary d n U).val := by
    rw [hcoeff,tensorUnitary_mul,Matrix.smul_mul]
  rw [gram,weightedIntegral,← integral_mul_right_eq_self
    (fun V => coefficient d n (X*(tensorUnitary d n U).val) V • (tensorUnitary d n V).val) U]
  simp_rw [hpoint]
  exact (mulRightCLM d n (tensorUnitary d n U).val).integral_comp_comm
    (integrable_weighted d n _ (continuous_coefficient d n X))

end GeneralizedChannelStein.InvariantIntegral
