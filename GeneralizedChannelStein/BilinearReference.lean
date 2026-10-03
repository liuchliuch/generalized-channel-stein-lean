import QuantumChannelStein.DiamondReferenceReduction
import QuantumChannelStein.DiamondHermitianReduction

/-! Two-sided pure-vector compression for arbitrary complex-linear maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelEntropy TraceNorm PureReferenceRecovery
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def crossMatrix (u v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp v))

theorem crossMatrix_gram (u v : EuclideanSpace ℂ ι) (hu : ‖u‖=1) :
    (crossMatrix u v)ᴴ*crossMatrix u v=pureMatrix v := by
  have ht := trace_pureMatrix_of_norm_one u hu
  ext i j
  simp only [crossMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.vecMulVec_apply,
    Pi.star_apply,map_mul,star_star,pureMatrix]
  have he : ∑ k, star (u k)*u k=(1:ℂ) := by
    simpa [pureMatrix,Matrix.trace,Matrix.diag,Matrix.vecMulVec_apply,mul_comm] using ht
  calc
    _ = v i*(∑ k,star (u k)*u k)*star (v j) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp only [StarMul.star_mul,star_star]
      ring
    _ = _ := by rw [he]; simp [Matrix.vecMulVec_apply]

theorem pureMatrix_idempotent (u : EuclideanSpace ℂ ι) (hu : ‖u‖=1) :
    pureMatrix u*pureMatrix u=pureMatrix u := by
  have h := crossMatrix_gram u u hu
  change (pureMatrix u)ᴴ*pureMatrix u=pureMatrix u at h
  rwa [(pureMatrix_positive u).isHermitian.eq] at h

theorem traceNorm_crossMatrix (u v : EuclideanSpace ℂ ι) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    TraceNorm.traceNorm (crossMatrix u v)=1 := by
  unfold TraceNorm.traceNorm
  rw [crossMatrix_gram u v hu]
  have hs : CFC.sqrt (pureMatrix v)=pureMatrix v :=
    (CFC.sqrt_eq_iff _ _ (pureMatrix_positive v).nonneg (pureMatrix_positive v).nonneg).mpr
      (pureMatrix_idempotent v hv)
  rw [hs,trace_pureMatrix_of_norm_one v hv]
  rfl

variable {a b r s : ℕ}

theorem amplify_reference_bilinear (Φ : MatrixMap a b)
    (A B : Matrix (Fin s) (Fin r) ℂ)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    MatrixMap.amplify Φ s ((A⊗ₖ(1:Operator a))*X*(B⊗ₖ(1:Operator a))ᴴ)=
      (A⊗ₖ(1:Operator b))*MatrixMap.amplify Φ r X*(B⊗ₖ(1:Operator b))ᴴ := by
  have hblock (u v : Fin s) :
      (fun k l => (((A⊗ₖ(1:Operator a))*X)*(B⊗ₖ(1:Operator a))ᴴ) (u,k) (v,l)) =
      ∑ x : Fin r, ∑ y : Fin r, (A u x*star (B v y)) • (fun k l => X (x,k) (y,l)) := by
    ext k l
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.kroneckerMap_apply,
      Matrix.one_apply,Fintype.sum_prod_type,Matrix.sum_apply,Matrix.smul_apply,
      mul_comm,mul_left_comm,mul_assoc,Finset.sum_mul,Finset.mul_sum,apply_ite]
    rw [Finset.sum_comm]
  ext ⟨u,i⟩ ⟨v,j⟩
  change Φ _ i j = _
  rw [hblock]
  simp [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.kroneckerMap_apply,
    Matrix.one_apply,Fintype.sum_prod_type,Matrix.sum_apply,Matrix.smul_apply,MatrixMap.amplify,
    mul_comm,mul_left_comm,mul_assoc,Finset.sum_mul,Finset.mul_sum,apply_ite]
  rw [Finset.sum_comm]

theorem reference_crossMatrix (A B : Matrix (Fin s) (Fin r) ℂ)
    (φ χ : UnitPureInput r a) (ψ ζ : UnitPureInput s a)
    (hψ : coefficientMatrix ψ=A*coefficientMatrix φ)
    (hζ : coefficientMatrix ζ=B*coefficientMatrix χ) :
    (A⊗ₖ(1:Operator a))*crossMatrix φ.val χ.val*(B⊗ₖ(1:Operator a))ᴴ=crossMatrix ψ.val ζ.val := by
  ext ⟨i,j⟩ ⟨k,l⟩
  have hψ' := congrFun (congrFun hψ i) j
  have hζ' := congrFun (congrFun hζ k) l
  change ψ.val (i,j)=_ at hψ'
  change ζ.val (k,l)=_ at hζ'
  simp only [crossMatrix,Matrix.vecMulVec_apply,Pi.star_apply]
  rw [hψ',hζ']
  simp [crossMatrix,coefficientMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply,Pi.star_apply,Matrix.kroneckerMap_apply,Matrix.one_apply,
    Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul,mul_comm,mul_left_comm,mul_assoc,apply_ite]

/-- Left and right Schmidt contractions may differ; no Hermiticity premise is imposed. -/
theorem cross_reference_traceNorm_le (Φ : MatrixMap a b) (ψ ζ : UnitPureInput r a) :
    ∃ φ χ : UnitPureInput a a,
      TraceNorm.traceNorm (MatrixMap.amplify Φ r (crossMatrix ψ.val ζ.val)) ≤
        TraceNorm.traceNorm (MatrixMap.amplify Φ a (crossMatrix φ.val χ.val)) := by
  let φ := TestingPrimal.densityInput (inputDensity ψ)
  let χ := TestingPrimal.densityInput (inputDensity ζ)
  obtain ⟨A,hA,hψ⟩ := exists_coefficient_contraction ψ
  obtain ⟨B,hB,hζ⟩ := exists_coefficient_contraction ζ
  have he := reference_crossMatrix A B φ χ ψ ζ hψ hζ
  refine ⟨φ,χ,?_⟩
  rw [←he,amplify_reference_bilinear]
  have hA' := (TensorNorm.kronecker_one_opNorm_le (r:=Fin b) A).trans hA
  have hB' := (TensorNorm.kronecker_one_opNorm_le (r:=Fin b) B).trans hB
  have ht := TraceNorm.traceNorm_nonneg (MatrixMap.amplify Φ a (crossMatrix φ.val χ.val))
  apply (traceNorm_sandwich_le _ _ _).trans
  rw [Matrix.l2_opNorm_conjTranspose]
  calc
    _ ≤ 1*TraceNorm.traceNorm (MatrixMap.amplify Φ a (crossMatrix φ.val χ.val))*1 := by
      gcongr
    _ = _ := by ring

end GeneralizedChannelStein
