import QuantumChannelStein.SharpFiniteFeasibility
import QuantumChannelStein.SandwichedRenyiTensor

/-! # Exact tensor multiplicativity of the supported weighted mean -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SupportedGeometricMean
open Matrix Pseudoinverse SandwichedRenyi
open scoped Kronecker MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
local instance geometricMeanTensorCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
local instance geometricMeanTensorCStar2 : CStarAlgebra (Matrix κ κ ℂ) := CStarAlgebra.mk
local instance geometricMeanTensorCStar3 : CStarAlgebra (Matrix (ι × κ) (ι × κ) ℂ) := CStarAlgebra.mk

theorem root_eq_rpow_half (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    root B hB = CFC.rpow B (1 / 2 : ℝ) := by
  unfold root
  rw [← hB.isHermitian.cfc_eq, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hB.nonneg]
  congr 1
  funext x
  exact Real.sqrt_eq_rpow x

theorem inverseSqrt_eq_rpow_neg_half (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    inverseSqrt B hB = CFC.rpow B (-1 / 2 : ℝ) := by
  unfold inverseSqrt
  rw [← hB.isHermitian.cfc_eq, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hB.nonneg]
  apply cfc_congr
  intro x hx
  dsimp only
  rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg]
  exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B).mp hB.nonneg x hx

theorem root_kronecker (B : Matrix ι ι ℂ) (D : Matrix κ κ ℂ)
    (hB : B.PosSemidef) (hD : D.PosSemidef) :
    root (B ⊗ₖ D) (MatrixMap.posSemidef_kronecker hB hD) = root B hB ⊗ₖ root D hD := by
  rw [root_eq_rpow_half, root_eq_rpow_half, root_eq_rpow_half, rpow_kronecker B D hB hD]

theorem inverseSqrt_kronecker (B : Matrix ι ι ℂ) (D : Matrix κ κ ℂ)
    (hB : B.PosSemidef) (hD : D.PosSemidef) :
    inverseSqrt (B ⊗ₖ D) (MatrixMap.posSemidef_kronecker hB hD) =
      inverseSqrt B hB ⊗ₖ inverseSqrt D hD := by
  rw [inverseSqrt_eq_rpow_neg_half, inverseSqrt_eq_rpow_neg_half,
    inverseSqrt_eq_rpow_neg_half, rpow_kronecker B D hB hD]

theorem mean_kronecker (p : ℝ) (A B : Matrix ι ι ℂ) (C D : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef) :
    mean p (B ⊗ₖ D) (MatrixMap.posSemidef_kronecker hB hD) (A ⊗ₖ C) =
      mean p B hB A ⊗ₖ mean p D hD C := by
  have hS₁ : (inverseSqrt B hB * A * inverseSqrt B hB).PosSemidef := by
    simpa only [(inverseSqrt_isHermitian B hB).eq] using
      hA.mul_mul_conjTranspose_same (inverseSqrt B hB)
  have hS₂ : (inverseSqrt D hD * C * inverseSqrt D hD).PosSemidef := by
    simpa only [(inverseSqrt_isHermitian D hD).eq] using
      hC.mul_mul_conjTranspose_same (inverseSqrt D hD)
  unfold mean
  rw [root_kronecker B D hB hD, inverseSqrt_kronecker B D hB hD]
  simp only [← Matrix.mul_kronecker_mul]
  rw [rpow_kronecker _ _ hS₁ hS₂]
  simp only [← Matrix.mul_kronecker_mul]

end QuantumChannelStein.SupportedGeometricMean
