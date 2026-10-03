import QuantumChannelStein.TraceNormCoordinates
import QuantumChannelStein.PureReferenceRecovery

/-! # Genuine input-sized reference reduction for pure diamond-norm tests -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.DiamondNorm
open Matrix ChannelEntropy PureReferenceRecovery TraceNorm
open scoped BigOperators Kronecker Matrix.Norms.L2Operator
variable {a b r s : ℕ}

/-- An arbitrary complex-linear map commutes with a reference congruence. -/
theorem amplify_reference_congr (Φ : MatrixMap a b) (A : Matrix (Fin s) (Fin r) ℂ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    MatrixMap.amplify Φ s (((A ⊗ₖ (1 : Operator a)) * X) * (A ⊗ₖ (1 : Operator a))ᴴ) =
      (A ⊗ₖ (1 : Operator b)) * MatrixMap.amplify Φ r X * (A ⊗ₖ (1 : Operator b))ᴴ := by
  have hblock (u v : Fin s) :
      (fun k l => (((A ⊗ₖ (1 : Operator a)) * X) * (A ⊗ₖ (1 : Operator a))ᴴ) (u,k) (v,l)) =
      ∑ x : Fin r, ∑ y : Fin r, (A u x * star (A v y)) • (fun k l => X (x,k) (y,l)) := by
    ext k l
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
      mul_comm, mul_left_comm, mul_assoc, Finset.sum_mul, Finset.mul_sum, apply_ite]
    rw [Finset.sum_comm]
  ext ⟨u,i⟩ ⟨v,j⟩
  change Φ _ i j = _
  rw [hblock]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
    MatrixMap.amplify, mul_comm, mul_left_comm, mul_assoc, Finset.sum_mul, Finset.mul_sum, apply_ite]
  rw [Finset.sum_comm]

/-- Every arbitrary-reference pure test is bounded by a canonical pure test
with reference dimension exactly the input dimension. This holds for every
complex-linear map, without a positivity premise. -/
theorem pure_reference_traceNorm_le (Φ : MatrixMap a b) (ψ : UnitPureInput r a) :
    ∃ φ : UnitPureInput a a,
      TraceNorm.traceNorm (MatrixMap.amplify Φ r (pureMatrix ψ.val)) ≤
        TraceNorm.traceNorm (MatrixMap.amplify Φ a (pureMatrix φ.val)) := by
  let φ := TestingPrimal.densityInput (inputDensity ψ)
  obtain ⟨A, hA, hcoeff⟩ := exists_coefficient_contraction ψ
  have hp : (A ⊗ₖ (1 : Operator a)) * pureMatrix φ.val * (A ⊗ₖ (1 : Operator a))ᴴ =
      pureMatrix ψ.val := by
    apply reference_conjugate_pure A φ ψ
    exact hcoeff
  refine ⟨φ, ?_⟩
  rw [← hp, amplify_reference_congr]
  have hB : ‖A ⊗ₖ (1 : Operator b)‖ ≤ 1 := (TensorNorm.kronecker_one_opNorm_le A).trans hA
  apply (traceNorm_sandwich_le _ _ _).trans
  rw [Matrix.l2_opNorm_conjTranspose]
  have ht := TraceNorm.traceNorm_nonneg (MatrixMap.amplify Φ a (pureMatrix φ.val))
  calc
    _ ≤ 1 * TraceNorm.traceNorm (MatrixMap.amplify Φ a (pureMatrix φ.val)) * 1 := by
      gcongr
    _ = _ := by ring

/-- The paper's pure-input, input-sized-reference expression. -/
def pureDiamondNorm (Φ : MatrixMap a b) : ENNReal :=
  ⨆ ψ : UnitPureInput a a,
    ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify Φ a (pureMatrix ψ.val)))

theorem pure_traceNorm_le_pureDiamondNorm (Φ : MatrixMap a b) (ψ : UnitPureInput r a) :
    ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify Φ r (pureMatrix ψ.val))) ≤ pureDiamondNorm Φ := by
  obtain ⟨φ,hφ⟩ := pure_reference_traceNorm_le Φ ψ
  exact (ENNReal.ofReal_le_ofReal hφ).trans (le_iSup (fun φ : UnitPureInput a a =>
    ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify Φ a (pureMatrix φ.val)))) φ)

/-- The pure expression is bounded by the full cb trace norm, with no reduction assumption. -/
theorem pureDiamondNorm_le_diamondNorm (Φ : MatrixMap a b) : pureDiamondNorm Φ ≤ diamondNorm Φ := by
  apply iSup_le
  intro ψ
  have hnorm : TraceNorm.traceNorm (pureMatrix ψ.val) ≤ 1 := by
    rw [traceNorm_of_posSemidef _ (pureMatrix_positive ψ.val), trace_pureMatrix_of_norm_one ψ.val ψ.property]
    norm_num
  exact le_iSup_of_le a (le_iSup_of_le ⟨pureMatrix ψ.val, hnorm⟩ le_rfl)

end QuantumChannelStein.DiamondNorm
