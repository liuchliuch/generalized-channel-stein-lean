import GeneralizedChannelStein.HaarAlgebra
import GeneralizedChannelStein.NormedTraceBound
import GeneralizedChannelStein.UnitaryPowerSpan
import GeneralizedChannelStein.InvariantOrbitDimension

/-! # Dimension-controlled genuine Haar reconstruction

The inverse Haar frame is identified with the left-regular character by
an actual finite-basis trace identity. No Schur orthogonality or spanning
oracle is introduced.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace GeneralizedChannelStein.InvariantIntegral
open QuantumChannelStein Matrix TensorPower TensorPermutation MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The tensor representation regarded as an element of its genuine span. -/
def spanUnitary (d n : ℕ) (U : UnitaryGroup d) : unitarySpan d n :=
  ⟨(tensorUnitary d n U).val,Submodule.subset_span ⟨U,rfl⟩⟩

def spanMul (d n : ℕ) (X Y : unitarySpan d n) : unitarySpan d n :=
  ⟨X.val*Y.val,unitarySpan_mul_mem d n X.property Y.property⟩

def leftRegular (d n : ℕ) (X : unitarySpan d n) : unitarySpan d n →L[ℂ] unitarySpan d n :=
  LinearMap.toContinuousLinearMap {
    toFun := spanMul d n X
    map_add' := by intro Y Z; apply Subtype.ext; exact Matrix.mul_add _ _ _
    map_smul' := by intro c Y; apply Subtype.ext; exact Matrix.mul_smul _ _ _ }

def coefficientMap (d n : ℕ) (U : UnitaryGroup d) : unitarySpan d n →ₗ[ℂ] ℂ where
  toFun X := coefficient d n X.val U
  map_add' X Y := coefficient_add d n X.val Y.val U
  map_smul' c X := coefficient_smul d n c X.val U

theorem continuous_spanUnitary (d n : ℕ) : Continuous (spanUnitary d n) :=
  (continuous_tensorUnitary_val d n).subtype_mk _

theorem gramOnSpan_eq_integral (d n : ℕ) (X : unitarySpan d n) :
    gramOnSpan d n X = ∫ U, coefficient d n X.val U • spanUnitary d n U ∂haar d := by
  have hi : Integrable (fun U => coefficient d n X.val U • spanUnitary d n U) (haar d) :=
    ((continuous_coefficient d n X.val).smul (continuous_spanUnitary d n)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply Subtype.ext
  exact (unitarySpan d n).subtypeL.integral_comp_comm hi

theorem gram_mul_left (d n : ℕ) {X : TensorOperator d n} (hX : X ∈ unitarySpan d n)
    (Y : TensorOperator d n) : gram d n (X*Y)=X*gram d n Y := by
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨U,rfl⟩ := hX; exact gram_mul_tensorUnitary_left d n U Y
  | zero => simp [gram,weightedIntegral,coefficient]
  | add X Z hX hZ ihX ihZ => simp only [Matrix.add_mul,gram_add,ihX,ihZ]
  | smul c X hX ih => simp only [Matrix.smul_mul,gram_smul,ih]

theorem gram_mul_right (d n : ℕ) {X : TensorOperator d n} (hX : X ∈ unitarySpan d n)
    (Y : TensorOperator d n) : gram d n (Y*X)=gram d n Y*X := by
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨U,rfl⟩ := hX; exact gram_mul_tensorUnitary_right d n U Y
  | zero => simp [gram,weightedIntegral,coefficient]
  | add X Z hX hZ ihX ihZ => simp only [Matrix.mul_add,gram_add,ihX,ihZ]
  | smul c X hX ih => simp only [Matrix.mul_smul,gram_smul,ih]

theorem gramInv_mul_left (d n : ℕ) (X Y : unitarySpan d n) :
    (gramEquiv d n).symm (spanMul d n X Y)=spanMul d n X ((gramEquiv d n).symm Y) := by
  apply (gramEquiv d n).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change X.val*Y.val=gram d n (X.val*((gramEquiv d n).symm Y).val)
  rw [gram_mul_left d n X.property]
  exact congrArg (fun Z : unitarySpan d n => X.val*Z.val) ((gramEquiv d n).apply_symm_apply Y).symm

theorem gramInv_mul_right (d n : ℕ) (X Y : unitarySpan d n) :
    (gramEquiv d n).symm (spanMul d n X Y)=spanMul d n ((gramEquiv d n).symm X) Y := by
  apply (gramEquiv d n).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change X.val*Y.val=gram d n (((gramEquiv d n).symm X).val*Y.val)
  rw [gram_mul_right d n Y.property]
  exact congrArg (fun Z : unitarySpan d n => Z.val*Y.val) ((gramEquiv d n).apply_symm_apply X).symm

/-- The trace of an arbitrary endomorphism is the actual inverse-frame coefficient integral. -/
theorem trace_eq_integral_inverse_frame (d n : ℕ)
    (T : unitarySpan d n →ₗ[ℂ] unitarySpan d n) :
    LinearMap.trace ℂ (unitarySpan d n) T =
      ∫ U, coefficient d n ((gramEquiv d n).symm (T (spanUnitary d n U))).val U ∂haar d := by
  classical
  let b := Module.finBasis ℂ (unitarySpan d n)
  let G := (gramEquiv d n).symm
  have hterm (i : Fin (Module.finrank ℂ (unitarySpan d n))) :
      b.coord i (T (b i)) =
        ∫ U, coefficient d n (G (b i)).val U * b.coord i (T (spanUnitary d n U)) ∂haar d := by
    let L := LinearMap.toContinuousLinearMap ((b.coord i).comp T)
    have hi : Integrable (fun U => coefficient d n (G (b i)).val U • spanUnitary d n U) (haar d) :=
      ((continuous_coefficient d n (G (b i)).val).smul (continuous_spanUnitary d n)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h := L.integral_comp_comm hi
    have hg : (∫ U, coefficient d n (G (b i)).val U • spanUnitary d n U ∂haar d) = b i := by
      rw [← gramOnSpan_eq_integral]
      exact (gramEquiv d n).apply_symm_apply (b i)
    rw [hg] at h
    simpa only [map_smul,smul_eq_mul] using h.symm
  have hpoint (U : UnitaryGroup d) :
      (∑ i, coefficient d n (G (b i)).val U * b.coord i (T (spanUnitary d n U))) =
        coefficient d n (G (T (spanUnitary d n U))).val U := by
    let K := (coefficientMap d n U).comp G.toLinearMap
    have h := congrArg K (b.sum_repr (T (spanUnitary d n U)))
    simp only [map_sum,map_smul,smul_eq_mul] at h
    simpa only [K,LinearMap.comp_apply,LinearEquiv.coe_coe,coefficientMap,
      LinearMap.coe_mk,AddHom.coe_mk,Module.Basis.coord_apply,mul_comm] using h
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply]
  change (∑ i, b.coord i (T (b i))) = _
  simp_rw [hterm]
  rw [← integral_finset_sum]
  · exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  · intro i hi
    exact ((continuous_coefficient d n (G (b i)).val).mul
      ((LinearMap.toContinuousLinearMap ((b.coord i).comp T)).continuous.comp
        (continuous_spanUnitary d n))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The left-regular trace is the ambient trace of the genuine inverse Haar frame. -/
theorem trace_leftRegular_eq (d n : ℕ) (X : unitarySpan d n) :
    LinearMap.trace ℂ (unitarySpan d n) (leftRegular d n X).toLinearMap =
      (((gramEquiv d n).symm X).val).trace := by
  rw [trace_eq_integral_inverse_frame]
  have hpoint (U : UnitaryGroup d) :
      coefficient d n ((gramEquiv d n).symm ((leftRegular d n X) (spanUnitary d n U))).val U =
        (((gramEquiv d n).symm X).val).trace := by
    change coefficient d n ((gramEquiv d n).symm (spanMul d n X (spanUnitary d n U))).val U = _
    rw [gramInv_mul_right]
    change ((tensorUnitary d n U).valᴴ * (((gramEquiv d n).symm X).val*(tensorUnitary d n U).val)).trace = _
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle]
    rw [tensorUnitary_adjoint,← tensorUnitary_mul,mul_inv_cancel,tensorUnitary_one,Matrix.one_mul]
  calc
    _ = ∫ _U : UnitaryGroup d, (((gramEquiv d n).symm X).val).trace ∂haar d :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = _ := by simp only [integral_const,probReal_univ,one_smul]

/-- The inverse-frame coefficient is exactly a finite left-regular character. -/
theorem inverse_coefficient_eq_regular_trace (d n : ℕ) (W : unitarySpan d n) (U : UnitaryGroup d) :
    coefficient d n ((gramEquiv d n).symm W).val U =
      LinearMap.trace ℂ (unitarySpan d n)
        (leftRegular d n (spanMul d n (spanUnitary d n U⁻¹) W)).toLinearMap := by
  rw [trace_leftRegular_eq,gramInv_mul_left]
  change ((tensorUnitary d n U).valᴴ*((gramEquiv d n).symm W).val).trace =
    ((tensorUnitary d n U⁻¹).val*((gramEquiv d n).symm W).val).trace
  rw [tensorUnitary_adjoint]

/-- The left-regular action is contractive for the inherited genuine matrix operator norm. -/
theorem norm_leftRegular_le (d n : ℕ) (X : unitarySpan d n) :
    ‖leftRegular d n X‖ ≤ ‖X.val‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro Y
  exact Matrix.l2_opNorm_mul X.val Y.val

/-- Dimension-sharp absolute coefficient bound, proved without a representation-theory oracle. -/
theorem norm_inverse_coefficient_le (d n : ℕ) (W : unitarySpan d n) (U : UnitaryGroup d) :
    ‖coefficient d n ((gramEquiv d n).symm W).val U‖ ≤
      (Module.finrank ℂ (unitarySpan d n) : ℝ)*‖W.val‖ := by
  rw [inverse_coefficient_eq_regular_trace]
  have hmul : ‖(spanMul d n (spanUnitary d n U⁻¹) W).val‖ ≤ ‖W.val‖ := by
    apply (Matrix.l2_opNorm_mul _ _).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_tensorUnitary_le d n U⁻¹) (norm_nonneg W.val)
  exact (NormedTraceBound.norm_trace_le_finrank_mul_norm _).trans
    (mul_le_mul_of_nonneg_left ((norm_leftRegular_le d n _).trans hmul) (Nat.cast_nonneg _))

/-- Literal equality between the actual span and actual permutation-invariant algebra. -/
theorem unitarySpan_eq_invariant (d n : ℕ) :
    unitarySpan d n=(invariantAlgebra (Fin d) n).toSubmodule :=
  UnitaryPowerSpan.span_unitary_tensor_powers d n

/-- Actual continuous Haar reconstruction with a polynomial coefficient bound.
Every algebraic and measure-theoretic ingredient is proved. -/
theorem invariant_integral_representation_polynomial (d n : ℕ) (W : TensorOperator d n)
    (hW : W ∈ invariantAlgebra (Fin d) n) (hWnorm : ‖W‖ ≤ 1) :
    ∃ f : UnitaryGroup d → ℂ, Continuous f ∧
      (∀ U, ‖f U‖ ≤ (((n+1)^(d*d) : ℕ) : ℝ)) ∧ weightedIntegral d n f=W := by
  have hmem : W ∈ unitarySpan d n := by rw [unitarySpan_eq_invariant]; exact hW
  let A : unitarySpan d n := ⟨W,hmem⟩
  let X := (gramEquiv d n).symm A
  refine ⟨coefficient d n X.val,continuous_coefficient d n X.val,?_,?_⟩
  · intro U
    have hdim : Module.finrank ℂ (unitarySpan d n) ≤ (n+1)^(d*d) := by
      rw [unitarySpan_eq_invariant]
      simpa only [Fintype.card_fin] using finrank_invariantAlgebra_le (Fin d) n
    have h := norm_inverse_coefficient_le d n A U
    exact h.trans ((mul_le_of_le_one_right (Nat.cast_nonneg _) hWnorm).trans (by exact_mod_cast hdim))
  · exact congrArg Subtype.val ((gramEquiv d n).apply_symm_apply A)

/-- The exact binomial coefficient mass in the paper's unitary integral representation. -/
theorem invariant_integral_representation (d n : ℕ) (hd : 0 < d) (W : TensorOperator d n)
    (hW : W ∈ invariantAlgebra (Fin d) n) (hWnorm : ‖W‖ ≤ 1) :
    ∃ f : UnitaryGroup d → ℂ, Continuous f ∧
      (∀ U, ‖f U‖ ≤ (((n+d^2-1).choose (d^2-1) : ℕ) : ℝ)) ∧ weightedIntegral d n f=W := by
  have hmem : W ∈ unitarySpan d n := by rw [unitarySpan_eq_invariant]; exact hW
  let A : unitarySpan d n := ⟨W,hmem⟩
  let X := (gramEquiv d n).symm A
  refine ⟨coefficient d n X.val,continuous_coefficient d n X.val,?_,?_⟩
  · intro U
    have hdim : Module.finrank ℂ (unitarySpan d n) ≤ (n+d^2-1).choose (d^2-1) := by
      rw [unitarySpan_eq_invariant]
      exact InvariantOrbitDimension.finrank_invariantAlgebra_le_binomial d n hd
    have h := norm_inverse_coefficient_le d n A U
    exact h.trans ((mul_le_of_le_one_right (Nat.cast_nonneg _) hWnorm).trans (by exact_mod_cast hdim))
  · exact congrArg Subtype.val ((gramEquiv d n).apply_symm_apply A)

end GeneralizedChannelStein.InvariantIntegral
