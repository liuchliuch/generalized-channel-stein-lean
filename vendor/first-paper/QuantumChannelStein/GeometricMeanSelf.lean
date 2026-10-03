import QuantumChannelStein.SharpDataProcessing
import QuantumChannelStein.SandwichedQuasiBound

/-! # Exact self-comparison and finite supported feasibility -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SupportedGeometricMean
open Matrix Pseudoinverse SandwichedRenyi
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] matrixCStar
variable {n : ℕ}

theorem supportProjection_idempotent (B : Operator n) (hB : B.PosSemidef) :
    supportProjection B hB * supportProjection B hB = supportProjection B hB := by
  calc
    _ = (B * pseudoinverse B hB) * (B * pseudoinverse B hB) := by rw [mul_pseudoinverse]
    _ = (B * pseudoinverse B hB * B) * pseudoinverse B hB := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [mul_pseudoinverse_mul, mul_pseudoinverse]

theorem supportProjection_isStarProjection (B : Operator n) (hB : B.PosSemidef) :
    IsStarProjection (supportProjection B hB) :=
  ⟨supportProjection_idempotent B hB, (supportProjection_isHermitian B hB).isSelfAdjoint⟩

theorem rpow_supportProjection (B : Operator n) (hB : B.PosSemidef) (p : ℝ) (hp : 0 < p) :
    CFC.rpow (supportProjection B hB) p = supportProjection B hB := by
  let P := supportProjection B hB
  have hP := supportProjection_isStarProjection B hB
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hP.nonneg]
  calc
    cfc (fun x : ℝ => x ^ p) P = cfc (id : ℝ → ℝ) P := by
      apply cfc_congr
      intro x hx
      have hmem := hP.isIdempotentElem.spectrum_subset ℝ hx
      rcases hmem with h | h
      · simp [h, Real.zero_rpow hp.ne']
      · simp only [Set.mem_singleton_iff] at h
        simp [h]
    _ = P := cfc_id' ℝ P

theorem inverseSqrt_self_sandwich (B : Operator n) (hB : B.PosSemidef) :
    inverseSqrt B hB * B * inverseSqrt B hB = supportProjection B hB := by
  calc
    _ = inverseSqrt B hB * (root B hB * root B hB) * inverseSqrt B hB := by rw [root_mul_root]
    _ = (inverseSqrt B hB * root B hB) * (root B hB * inverseSqrt B hB) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [inverseSqrt_mul_root, root_mul_inverseSqrt, supportProjection_idempotent]

theorem mean_scaled_self (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (B : Operator n) (hB : B.PosSemidef) : mean p B hB (c • B) = (c ^ p) • B := by
  have hP := supportProjection_isStarProjection B hB
  unfold mean
  rw [Matrix.mul_smul, Matrix.smul_mul, inverseSqrt_self_sandwich,
    rpow_real_smul _ hP.nonneg.posSemidef c p hc, rpow_supportProjection B hB p hp,
    Matrix.mul_smul, Matrix.smul_mul, root_mul_supportProjection, root_mul_root]

end QuantumChannelStein.SupportedGeometricMean
