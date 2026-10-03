import QuantumChannelStein.MatrixCornerCalculus
import QuantumChannelStein.SpectralDecompositionCFC

/-! # Dimension-free rectangular Hansen inequality
Zero-padding embeds arbitrary rectangular contractions into square matrices.
The zero eigenspaces are retained by the positive-power corner calculus.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QuantumChannelStein.MatrixCornerCalculus
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
local instance rectangularPowerCompressionCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
local instance rectangularPowerCompressionCStar2 : CStarAlgebra (Matrix κ κ ℂ) := CStarAlgebra.mk
local instance rectangularPowerCompressionCStar3 : CStarAlgebra (Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) := CStarAlgebra.mk
local instance rectangularPowerCompressionCStar4 : CStarAlgebra (Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ) := CStarAlgebra.mk

/-- Lower-right corner obtained by swapping the two summands. -/
def lowerCorner (A : Matrix κ κ ℂ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ :=
  Matrix.reindex (Equiv.sumComm κ ι) (Equiv.sumComm κ ι) (cornerHom κ ι A)

theorem lowerCorner_eq (A : Matrix κ κ ℂ) :
    lowerCorner (ι := ι) A = fromBlocks 0 0 0 A := by
  ext i j
  cases i <;> cases j <;> rfl

theorem lowerCorner_nonneg {A : Matrix κ κ ℂ} (hA : 0 ≤ A) :
    0 ≤ lowerCorner (ι := ι) A := by
  exact ((corner_nonneg (κ := ι) hA).posSemidef.submatrix (Equiv.sumComm κ ι).symm).nonneg

theorem lowerCorner_rpow (A : Matrix κ κ ℂ) (hA : A.PosSemidef)
    (p : ℝ) (hp : 0 < p) :
    lowerCorner (ι := ι) (CFC.rpow A p) = CFC.rpow (lowerCorner (ι := ι) A) p := by
  have hc := (corner_nonneg (κ := ι) hA.nonneg).posSemidef
  have hl := (lowerCorner_nonneg (ι := ι) hA.nonneg).posSemidef
  have he : CFC.rpow (lowerCorner (ι := ι) A) p =
      cfc (fun x : ℝ => x ^ p) (lowerCorner (ι := ι) A) := by
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hl.nonneg]
  rw [he]
  unfold lowerCorner
  rw [corner_rpow A hA p hp, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hc.nonneg]
  exact (SpectralDecomposition.cfc_reindex (Equiv.sumComm κ ι)
    (cornerHom κ ι A) hc.isHermitian (fun x : ℝ => x ^ p)).symm

theorem lowerCorner_le_iff (A B : Matrix κ κ ℂ) :
    lowerCorner (ι := ι) A ≤ lowerCorner (ι := ι) B ↔ A ≤ B := by
  constructor
  · intro h
    have hh := (sub_nonneg.mpr h).posSemidef.submatrix Sum.inr
    have heq : (lowerCorner (ι := ι) B - lowerCorner (ι := ι) A).submatrix Sum.inr Sum.inr = B - A := by
      ext i j
      simp [lowerCorner_eq]
    rw [heq] at hh
    exact sub_nonneg.mp hh.nonneg
  · intro h
    have hh := lowerCorner_nonneg (ι := ι) (sub_nonneg.mpr h)
    have heq : lowerCorner (ι := ι) (B - A) = lowerCorner B - lowerCorner A := by
      simp only [lowerCorner, map_sub]
      rfl
    rw [heq] at hh
    exact sub_nonneg.mp hh

/-- Off-diagonal zero padding preserves a rectangular contraction bound. -/
theorem offDiagonal_norm_le_one (X : Matrix ι κ ℂ) (hX : ‖X‖ ≤ 1) :
    ‖fromBlocks (0 : Matrix ι ι ℂ) X (0 : Matrix κ ι ℂ) 0‖ ≤ 1 := by
  let Y := fromBlocks (0 : Matrix ι ι ℂ) X (0 : Matrix κ ι ℂ) 0
  have hgram := gram_le_one_of_norm_le_one X hX
  have hc := corner_nonneg (κ := κ) hgram.nonneg
  have hl := lowerCorner_nonneg (ι := ι) (show (0 : Matrix κ κ ℂ) ≤ 1 from zero_le_one)
  have heq : 1 - Y * Yᴴ = cornerHom ι κ (1 - X * Xᴴ) + lowerCorner (ι := ι) (1 : Matrix κ κ ℂ) := by
    simp only [Y, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_zero,
      Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, cornerHom, lowerCorner_eq]
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply]
  have hg : (1 - Y * Yᴴ).PosSemidef := by rw [heq]; exact (add_nonneg hc hl).posSemidef
  obtain ⟨D, hD, hn⟩ := Factorization.matrix_factorization Y (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ)
    (t := 1) zero_le_one (by simpa using hg)
  simpa using (show ‖Y‖ ≤ Real.sqrt 1 by simpa [hD] using hn)

/-- Hansen's inequality for a genuinely rectangular contraction, with arbitrary
finite input and output dimensions and singular positive operators. -/
theorem rectangular_rpow_compression (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (A : Matrix ι ι ℂ) (X : Matrix ι κ ℂ)
    (hA : A.PosSemidef) (hX : ‖X‖ ≤ 1) :
    Xᴴ * CFC.rpow A p * X ≤ CFC.rpow (Xᴴ * A * X) p := by
  let Y := fromBlocks (0 : Matrix ι ι ℂ) X (0 : Matrix κ ι ℂ) 0
  have hprod (B : Matrix ι ι ℂ) :
      Yᴴ * cornerHom ι κ B * Y = lowerCorner (ι := ι) (Xᴴ * B * X) := by
    simp [Y, cornerHom, lowerCorner_eq, fromBlocks_conjTranspose, fromBlocks_multiply]
  have hc := PowerCompression.matrix_rpow_compression p hp (cornerHom ι κ A) Y
    (corner_nonneg (κ := κ) hA.nonneg).posSemidef (offDiagonal_norm_le_one X hX)
  rw [← corner_rpow A hA p hp.1, hprod, hprod,
    ← lowerCorner_rpow (Xᴴ * A * X) (hA.conjTranspose_mul_mul_same X) p hp.1] at hc
  exact (lowerCorner_le_iff (ι := ι) _ _).mp hc

end QuantumChannelStein.MatrixCornerCalculus
