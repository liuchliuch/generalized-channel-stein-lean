import QuantumChannelStein.GeometricMeanBlocks

/-! # Genuine supported geometric-mean concavity
The weights enter as explicit rectangular matrix factors, not an assumed
joint-concavity interface. Singular alternatives remain allowed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QuantumChannelStein.SupportedGeometricMean
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance geometricMeanConcavityCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk

theorem sqrt_identity_congruence (c : ℝ) (hc : 0 ≤ c) (A : Matrix ι ι ℂ) :
    (Real.sqrt c • (1 : Matrix ι ι ℂ)) * A * (Real.sqrt c • (1 : Matrix ι ι ℂ))ᴴ = c • A := by
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [← pow_two, Real.sq_sqrt hc]

theorem superadditive (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (A B C D : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
    (h₁ : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin)
    (h₂ : LinearMap.ker D.mulVecLin ≤ LinearMap.ker C.mulVecLin) :
    mean p B hB A + mean p D hD C ≤ mean p (B + D) (hB.add hD) (A + C) := by
  have h := two_transformers p hp A B C D hA hB hC hD h₁ h₂
    (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
  have heq := mean_congr p
    ((hB.mul_mul_conjTranspose_same (1 : Matrix ι ι ℂ)).add
      (hD.mul_mul_conjTranspose_same (1 : Matrix ι ι ℂ))) (hB.add hD)
    (show (1 : Matrix ι ι ℂ) * B * (1 : Matrix ι ι ℂ)ᴴ + 1 * D * (1 : Matrix ι ι ℂ)ᴴ = B + D by simp)
    (show (1 : Matrix ι ι ℂ) * A * (1 : Matrix ι ι ℂ)ᴴ + 1 * C * (1 : Matrix ι ι ℂ)ᴴ = A + C by simp)
  rw [heq] at h
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using h

theorem jointly_concave (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (A B C D : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
    (h₁ : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin)
    (h₂ : LinearMap.ker D.mulVecLin ≤ LinearMap.ker C.mulVecLin)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • mean p B hB A + t • mean p D hD C ≤
      mean p ((1 - t) • B + t • D)
        ((hB.smul (sub_nonneg.mpr ht1)).add (hD.smul ht0)) ((1 - t) • A + t • C) := by
  let F := Real.sqrt (1 - t) • (1 : Matrix ι ι ℂ)
  let G := Real.sqrt t • (1 : Matrix ι ι ℂ)
  have h := two_transformers p hp A B C D hA hB hC hD h₁ h₂ F G
  have hF (X : Matrix ι ι ℂ) : F * X * Fᴴ = (1 - t) • X :=
    sqrt_identity_congruence (1 - t) (sub_nonneg.mpr ht1) X
  have hG (X : Matrix ι ι ℂ) : G * X * Gᴴ = t • X :=
    sqrt_identity_congruence t ht0 X
  have hright := mean_congr p
    ((hB.mul_mul_conjTranspose_same F).add (hD.mul_mul_conjTranspose_same G))
    ((hB.smul (sub_nonneg.mpr ht1)).add (hD.smul ht0))
    (show F * B * Fᴴ + G * D * Gᴴ = (1 - t) • B + t • D by rw [hF, hG])
    (show F * A * Fᴴ + G * C * Gᴴ = (1 - t) • A + t • C by rw [hF, hG])
  rw [hright, hF, hG] at h
  exact h

end QuantumChannelStein.SupportedGeometricMean
