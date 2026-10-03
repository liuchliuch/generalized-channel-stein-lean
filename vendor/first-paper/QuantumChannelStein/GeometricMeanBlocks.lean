import QuantumChannelStein.MatrixBlockCalculus

/-! # Direct sums and two-operation transformer inequality -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QuantumChannelStein.SupportedGeometricMean
open Matrix Pseudoinverse MatrixBlockCalculus
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq η]
local instance geometricMeanBlocksCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
local instance geometricMeanBlocksCStar2 : CStarAlgebra (Matrix κ κ ℂ) := CStarAlgebra.mk
local instance geometricMeanBlocksCStar3 : CStarAlgebra (Matrix η η ℂ) := CStarAlgebra.mk
local instance geometricMeanBlocksCStar4 : CStarAlgebra (Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) := CStarAlgebra.mk

theorem mean_fromBlocks (p : ℝ)
    (A B : Matrix ι ι ℂ) (C D : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef) :
    mean p (fromBlocks B 0 0 D) (fromBlocks_positive B D hB hD) (fromBlocks A 0 0 C) =
      fromBlocks (mean p B hB A) 0 0 (mean p D hD C) := by
  have hS₁ : (inverseSqrt B hB * A * inverseSqrt B hB).PosSemidef := by
    simpa only [(inverseSqrt_isHermitian B hB).eq] using
      hA.mul_mul_conjTranspose_same (inverseSqrt B hB)
  have hS₂ : (inverseSqrt D hD * C * inverseSqrt D hD).PosSemidef := by
    simpa only [(inverseSqrt_isHermitian D hD).eq] using
      hC.mul_mul_conjTranspose_same (inverseSqrt D hD)
  unfold mean
  rw [root_fromBlocks B D hB hD, inverseSqrt_fromBlocks B D hB hD]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [rpow_fromBlocks _ _ hS₁ hS₂]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem block_support (A B : Matrix ι ι ℂ) (C D : Matrix κ κ ℂ)
    (h₁ : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin)
    (h₂ : LinearMap.ker D.mulVecLin ≤ LinearMap.ker C.mulVecLin) :
    LinearMap.ker (fromBlocks B 0 0 D).mulVecLin ≤
      LinearMap.ker (fromBlocks A 0 0 C).mulVecLin := by
  intro x hx
  change (fromBlocks B 0 0 D) *ᵥ x = 0 at hx
  change (fromBlocks A 0 0 C) *ᵥ x = 0
  have hb : B *ᵥ (x ∘ Sum.inl) = 0 := by
    ext i
    have h := congrFun hx (Sum.inl i)
    simpa [fromBlocks_mulVec] using h
  have hd : D *ᵥ (x ∘ Sum.inr) = 0 := by
    ext i
    have h := congrFun hx (Sum.inr i)
    simpa [fromBlocks_mulVec] using h
  have ha : A *ᵥ (x ∘ Sum.inl) = 0 := h₁ hb
  have hc : C *ᵥ (x ∘ Sum.inr) = 0 := h₂ hd
  simp [fromBlocks_mulVec, ha, hc, Sum.elim_zero_zero]

theorem two_transformers (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (A B : Matrix ι ι ℂ) (C D : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
    (h₁ : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin)
    (h₂ : LinearMap.ker D.mulVecLin ≤ LinearMap.ker C.mulVecLin)
    (F : Matrix η ι ℂ) (G : Matrix η κ ℂ) :
    F * mean p B hB A * Fᴴ + G * mean p D hD C * Gᴴ ≤
      mean p (F * B * Fᴴ + G * D * Gᴴ)
        ((hB.mul_mul_conjTranspose_same F).add (hD.mul_mul_conjTranspose_same G))
        (F * A * Fᴴ + G * C * Gᴴ) := by
  have h := transformer p hp (fromBlocks A 0 0 C) (fromBlocks B 0 0 D)
    (fromBlocks_positive A C hA hC) (fromBlocks_positive B D hB hD)
    (block_support A B C D h₁ h₂) (fromCols F G)
  have hdiag (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) :
      fromCols F G * fromBlocks U 0 0 V * (fromCols F G)ᴴ = F * U * Fᴴ + G * V * Gᴴ := by
    simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose,
      fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, fromCols_mul_fromRows]
  have hright := mean_congr p
    ((fromBlocks_positive B D hB hD).mul_mul_conjTranspose_same (fromCols F G))
    ((hB.mul_mul_conjTranspose_same F).add (hD.mul_mul_conjTranspose_same G))
    (hdiag B D) (hdiag A C)
  have hleft : fromCols F G * mean p (fromBlocks B 0 0 D)
      (fromBlocks_positive B D hB hD) (fromBlocks A 0 0 C) * (fromCols F G)ᴴ =
      F * mean p B hB A * Fᴴ + G * mean p D hD C * Gᴴ := by
    rw [mean_fromBlocks p A B C D hA hB hC hD]
    exact hdiag _ _
  rw [hleft, hright] at h
  exact h


end QuantumChannelStein.SupportedGeometricMean
