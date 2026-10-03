import QuantumChannelStein.PseudoinverseSupport

/-! # Supported positive-semidefinite weighted geometric mean
The formula is used only with its explicit support condition. It must not be
identified with the unrestricted singular Kubo–Ando formula without proof.
The transformer inequality below is proved for arbitrary rectangular maps.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QuantumChannelStein.SupportedGeometricMean
open Matrix Pseudoinverse
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
local instance supportedGeometricMeanCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
local instance supportedGeometricMeanCStar2 : CStarAlgebra (Matrix κ κ ℂ) := CStarAlgebra.mk

/-- Weighted geometric mean on the support of the first positive argument. -/
def mean (p : ℝ) (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  root B hB * CFC.rpow (inverseSqrt B hB * A * inverseSqrt B hB) p * root B hB

theorem mean_congr (p : ℝ) {B C A D : Matrix ι ι ℂ}
    (hB : B.PosSemidef) (hC : C.PosSemidef) (hBC : B = C) (hAD : A = D) :
    mean p B hB A = mean p C hC D := by
  subst C
  subst D
  rfl

theorem mean_positive (p : ℝ) (B : Matrix ι ι ℂ) (hB : B.PosSemidef)
    (A : Matrix ι ι ℂ) : (mean p B hB A).PosSemidef := by
  simpa only [mean, (root_isHermitian B hB).eq] using
    (CFC.rpow_nonneg.posSemidef.mul_mul_conjTranspose_same (root B hB))

/-- Actual rectangular transformer inequality, with the singular-support
hypothesis explicit and no assumption on the rank of the transformer. -/
theorem transformer (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin)
    (F : Matrix κ ι ℂ) :
    F * mean p B hB A * Fᴴ ≤
      mean p (F * B * Fᴴ) (hB.mul_mul_conjTranspose_same F) (F * A * Fᴴ) := by
  let B' := F * B * Fᴴ
  let hB' : B'.PosSemidef := hB.mul_mul_conjTranspose_same F
  let T := F * root B hB
  let D := inverseSqrt B' hB' * T
  let S := inverseSqrt B hB * A * inverseSqrt B hB
  have hS : S.PosSemidef := by
    simpa only [S, (inverseSqrt_isHermitian B hB).eq] using
      hA.mul_mul_conjTranspose_same (inverseSqrt B hB)
  have hgram : T * Tᴴ = B' := by
    simp only [T, B', Matrix.conjTranspose_mul, (root_isHermitian B hB).eq]
    calc
      _ = F * (root B hB * root B hB) * Fᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [root_mul_root]
  have hDnorm : ‖D‖ ≤ 1 := by
    exact inverseSqrt_mul_norm_of_gram T B' hB' hgram
  have hRD : root B' hB' * D = T := by
    change root B' hB' * (inverseSqrt B' hB' * T) = T
    rw [← Matrix.mul_assoc, root_mul_inverseSqrt]
    exact supportProjection_mul_of_gram T B' hB' hgram
  have hDS : D * S * Dᴴ = inverseSqrt B' hB' * (F * A * Fᴴ) * inverseSqrt B' hB' := by
    simp only [D, T, Matrix.conjTranspose_mul, (inverseSqrt_isHermitian B' hB').eq,
      (root_isHermitian B hB).eq]
    calc
      _ = inverseSqrt B' hB' * F * (root B hB * S * root B hB) * Fᴴ * inverseSqrt B' hB' := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [show root B hB * S * root B hB = A from reconstruct_of_ker_le A B hA hB hs]; simp only [Matrix.mul_assoc]
  have hc := MatrixCornerCalculus.rectangular_rpow_compression p hp S Dᴴ hS
    (by simpa only [Matrix.l2_opNorm_conjTranspose] using hDnorm)
  simp only [Matrix.conjTranspose_conjTranspose] at hc
  have hh := (sub_nonneg.mpr hc).posSemidef.mul_mul_conjTranspose_same (root B' hB')
  have hh' : root B' hB' * (D * CFC.rpow S p * Dᴴ) * root B' hB' ≤
      root B' hB' * CFC.rpow (D * S * Dᴴ) p * root B' hB' := by
    apply sub_nonneg.mp
    simpa only [(root_isHermitian B' hB').eq, Matrix.mul_sub, Matrix.sub_mul] using hh.nonneg
  rw [hDS] at hh'
  have hleft : root B' hB' * (D * CFC.rpow S p * Dᴴ) * root B' hB' = F * mean p B hB A * Fᴴ := by
    calc
      _ = (root B' hB' * D) * CFC.rpow S p * (root B' hB' * D)ᴴ := by
        simp only [Matrix.conjTranspose_mul, (root_isHermitian B' hB').eq, Matrix.mul_assoc]
      _ = T * CFC.rpow S p * Tᴴ := by rw [hRD]
      _ = _ := by simp only [T, mean, S, Matrix.conjTranspose_mul, (root_isHermitian B hB).eq, Matrix.mul_assoc]
  rw [hleft] at hh'
  exact hh'

end QuantumChannelStein.SupportedGeometricMean
