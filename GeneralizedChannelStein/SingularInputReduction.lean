import GeneralizedChannelStein.BilinearReference

/-! Actual SVD reduction for arbitrary matrices and arbitrary complex-linear maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace GeneralizedChannelStein.SingularInputReduction
open QuantumChannelStein Matrix ChannelEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A column of the actual unitary singular-vector matrix. -/
def unitaryColumn (U : Matrix.unitaryGroup ι ℂ) (i : ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun j => (U:Matrix ι ι ℂ) j i)

theorem unitaryColumn_norm (U : Matrix.unitaryGroup ι ℂ) (i : ι) : ‖unitaryColumn U i‖=1 := by
  have h := congrArg (fun A : Matrix ι ι ℂ => (A i i).re) (Unitary.coe_star_mul_self U)
  have hsum : ∑ j,Complex.normSq ((U:Matrix ι ι ℂ) j i)=1 := by
    simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      ← Complex.normSq_eq_conj_mul_self] using h
  have hnorm : ‖unitaryColumn U i‖^2=1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [unitaryColumn,Complex.normSq_eq_norm_sq] using hsum
  nlinarith [norm_nonneg (unitaryColumn U i)]


theorem unitary_diagonal_cross_sum (U V : Matrix.unitaryGroup ι ℂ) (s : ι → ℝ) :
    (U:Matrix ι ι ℂ)*Matrix.diagonal (fun i => (s i:ℂ))*(V:Matrix ι ι ℂ)ᴴ =
      ∑ i,s i•crossMatrix (unitaryColumn U i) (unitaryColumn V i) := by
  ext i j
  simp [Matrix.mul_apply,Matrix.diagonal,Matrix.conjTranspose_apply,Matrix.sum_apply,
    Matrix.smul_apply,crossMatrix,unitaryColumn,Matrix.vecMulVec_apply,
    Pi.star_apply,Complex.real_smul,mul_comm,mul_left_comm,mul_assoc]

variable {a b r : ℕ}

def columnInput (U : Matrix.unitaryGroup (Fin r × Fin a) ℂ) (i : Fin r × Fin a) : UnitPureInput r a :=
  ⟨unitaryColumn U i,unitaryColumn_norm U i⟩

/-- Both vectors in each rank-one term are normalized actual reference-assisted
inputs. Singular values are nonnegative and sum to the actual trace norm.
No Hermiticity or nonzero-matrix premise is imposed. -/
theorem singular_cross_decomposition (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    ∃ s : (Fin r × Fin a) → ℝ, ∃ u v : (Fin r × Fin a) → UnitPureInput r a,
      (∀ i,0≤s i) ∧ (∑ i,s i)=TraceNorm.traceNorm X ∧
      X=∑ i,s i•crossMatrix (u i).val (v i).val := by
  let hH : (Xᴴ*X).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self X
  obtain ⟨U,V,hX⟩ := TraceNorm.exists_svd_sqrt_eigenvalues X
  refine ⟨fun i => Real.sqrt (hH.eigenvalues i),columnInput U,columnInput V,
    fun i => Real.sqrt_nonneg _,?_,?_⟩
  · exact (TraceNorm.traceNorm_eq_sum_sqrt_eigenvalues X).symm
  · exact hX.trans (unitary_diagonal_cross_sum U V (fun i => Real.sqrt (hH.eigenvalues i)))

/-- Bounds on every normalized cross matrix control every input matrix by its
trace norm. The map is arbitrary and need not preserve Hermiticity. -/
theorem arbitrary_traceNorm_bound (Φ : MatrixMap a b) (M : ℝ)
    (hcross : ∀ u v : UnitPureInput r a,
      TraceNorm.traceNorm (MatrixMap.amplify Φ r (crossMatrix u.val v.val))≤M)
    (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    TraceNorm.traceNorm (MatrixMap.amplify Φ r X)≤M*TraceNorm.traceNorm X := by
  obtain ⟨s,u,v,hs,hsum,hX⟩ := singular_cross_decomposition X
  have heq : MatrixMap.amplify Φ r X=∑ i,s i•MatrixMap.amplify Φ r (crossMatrix (u i).val (v i).val) := by
    conv_lhs => rw [hX]
    change DiamondNorm.amplifyLinear Φ r _=_
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := (DiamondNorm.amplifyLinear Φ r).map_smul (s i:ℂ) (crossMatrix (u i).val (v i).val)
    simpa only [DiamondNorm.amplifyLinear,LinearMap.coe_mk,AddHom.coe_mk,Complex.real_smul] using h
  rw [heq]
  calc
    _ ≤ ∑ i,TraceNorm.traceNorm (s i•MatrixMap.amplify Φ r (crossMatrix (u i).val (v i).val)) :=
      TraceNorm.traceNorm_sum_le _ _
    _ = ∑ i,s i*TraceNorm.traceNorm (MatrixMap.amplify Φ r (crossMatrix (u i).val (v i).val)) := by
      simp only [TraceNorm.traceNorm_real_smul,abs_of_nonneg (hs _)]
    _ ≤ ∑ i,s i*M := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcross _ _) (hs i)
    _ = _ := by rw [← Finset.sum_mul,hsum,mul_comm]

end GeneralizedChannelStein.SingularInputReduction
