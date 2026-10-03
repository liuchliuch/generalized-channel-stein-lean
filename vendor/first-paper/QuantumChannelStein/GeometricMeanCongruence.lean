import QuantumChannelStein.GeometricMeanKraus

/-! # Exact supported geometric-mean congruence under an invertible matrix
Both directions follow from the proved singular transformer inequality.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SupportedGeometricMean
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance geometricMeanCongruenceCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk

theorem undo_congruence (F G X : Matrix ι ι ℂ) (hGF : G * F = 1) :
    G * (F * X * Fᴴ) * Gᴴ = X := by
  calc
    _ = (G * F) * X * (G * F)ᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = X := by rw [hGF]; simp

theorem congruence_mono (F A B : Matrix ι ι ℂ) (hAB : A ≤ B) :
    F * A * Fᴴ ≤ F * B * Fᴴ := by
  apply sub_nonneg.mp
  have h := (sub_nonneg.mpr hAB).posSemidef.mul_mul_conjTranspose_same F
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using h.nonneg

theorem mean_congruence (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin)
    (F G : Matrix ι ι ℂ) (hFG : F * G = 1) (hGF : G * F = 1) :
    mean p (F * B * Fᴴ) (hB.mul_mul_conjTranspose_same F) (F * A * Fᴴ) =
      F * mean p B hB A * Fᴴ := by
  apply le_antisymm _ (transformer p hp A B hA hB hs F)
  have hsupport : LinearMap.ker (F * B * Fᴴ).mulVecLin ≤
      LinearMap.ker (F * A * Fᴴ).mulVecLin := by
    simpa [krausSum] using krausSum_support ({()} : Finset Unit) (fun _ => F) A B hA hB hs
  have hrev := transformer p hp (F * A * Fᴴ) (F * B * Fᴴ)
    (hA.mul_mul_conjTranspose_same F) (hB.mul_mul_conjTranspose_same F) hsupport G
  have hr := mean_congr p
    ((hB.mul_mul_conjTranspose_same F).mul_mul_conjTranspose_same G) hB
    (undo_congruence F G B hGF) (undo_congruence F G A hGF)
  rw [hr] at hrev
  have hh := congruence_mono F _ _ hrev
  rw [undo_congruence G F _ hFG] at hh
  exact hh

end QuantumChannelStein.SupportedGeometricMean
