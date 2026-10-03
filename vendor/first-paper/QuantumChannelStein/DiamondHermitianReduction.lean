import QuantumChannelStein.DiamondReferenceReduction

/-! # Actual Hermitian spectral pure-state reduction for diamond-norm tests -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.DiamondNorm
open Classical
open Matrix hiding traceNorm
open ChannelEntropy TraceNorm
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b r : ℕ}

/-- A normalized eigenvector, retained as an actual reference-assisted pure input. -/
def spectralPureInput (H : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) (hH : H.IsHermitian)
    (i : Fin r × Fin a) : UnitPureInput r a :=
  ⟨hH.eigenvectorBasis i, hH.eigenvectorBasis.norm_eq_one i⟩

/-- The full signed spectral decomposition into normalized rank-one input matrices. -/
theorem hermitian_spectral_sum (H : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) (hH : H.IsHermitian) :
    H = ∑ i : Fin r × Fin a, hH.eigenvalues i • pureMatrix (spectralPureInput H hH i).val := by
  have hs := hH.spectral_theorem
  change H = (hH.eigenvectorUnitary : Matrix _ _ ℂ) *
    Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * (hH.eigenvectorUnitary : Matrix _ _ ℂ)ᴴ at hs
  conv_lhs => rw [hs]
  ext i j
  simp [Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, pureMatrix, spectralPureInput,
    Matrix.vecMulVec_apply, Matrix.sum_apply, Matrix.smul_apply, Pi.star_apply, Complex.real_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Amplification remains genuinely linear on the complete reference matrix space. -/
def amplifyLinear (Φ : MatrixMap a b) (r : ℕ) :
    Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ →ₗ[ℂ]
      Matrix (Fin r × Fin b) (Fin r × Fin b) ℂ where
  toFun := MatrixMap.amplify Φ r
  map_add' X Y := by
    ext ⟨u,i⟩ ⟨v,j⟩
    exact congrFun (congrFun (Φ.map_add (fun k l => X (u,k) (v,l)) (fun k l => Y (u,k) (v,l))) i) j
  map_smul' c X := by
    ext ⟨u,i⟩ ⟨v,j⟩
    exact congrFun (congrFun (Φ.map_smul c (fun k l => X (u,k) (v,l))) i) j

/-- A bound on all actual pure inputs bounds every Hermitian input by its
trace norm, using the signed spectral expansion and true norm homogeneity. -/
theorem hermitian_traceNorm_bound (Φ : MatrixMap a b) (M : ℝ)
    (hpure : ∀ ψ : UnitPureInput r a, traceNorm (MatrixMap.amplify Φ r (pureMatrix ψ.val)) ≤ M)
    (H : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) (hH : H.IsHermitian) :
    traceNorm (MatrixMap.amplify Φ r H) ≤ M * traceNorm H := by
  have heq : MatrixMap.amplify Φ r H = ∑ i : Fin r × Fin a,
      hH.eigenvalues i • MatrixMap.amplify Φ r (pureMatrix (spectralPureInput H hH i).val) := by
    conv_lhs => rw [hermitian_spectral_sum H hH]
    change amplifyLinear Φ r _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h := (amplifyLinear Φ r).map_smul (hH.eigenvalues i : ℂ) (pureMatrix (spectralPureInput H hH i).val)
    simpa only [amplifyLinear, LinearMap.coe_mk, AddHom.coe_mk, Complex.real_smul] using h
  rw [heq]
  calc
    _ ≤ ∑ i : Fin r × Fin a, traceNorm
        (hH.eigenvalues i • MatrixMap.amplify Φ r (pureMatrix (spectralPureInput H hH i).val)) :=
      traceNorm_sum_le _ _
    _ = ∑ i : Fin r × Fin a, |hH.eigenvalues i| *
        traceNorm (MatrixMap.amplify Φ r (pureMatrix (spectralPureInput H hH i).val)) := by
      simp only [traceNorm_real_smul]
    _ ≤ ∑ i : Fin r × Fin a, |hH.eigenvalues i| * M :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpure _) (abs_nonneg _)
    _ = M * traceNorm H := by
      rw [← Finset.sum_mul, traceNorm_eq_matrixTraceNorm,
        Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues hH]
      exact mul_comm _ _

end QuantumChannelStein.DiamondNorm
