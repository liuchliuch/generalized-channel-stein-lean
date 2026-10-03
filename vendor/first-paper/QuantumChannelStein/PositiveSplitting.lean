import QuantumChannelStein.Testing
import QuantumChannelStein.Factorization
import QuantumChannelStein.PseudoinverseCalculus
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Splitting a dominated Gram matrix
A rectangular Douglas factorization against concatenated square roots gives
the two positive summands needed in Proposition 4.2, including singular matrices.
-/
noncomputable section
namespace QuantumChannelStein
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem gram_le_one_of_norm_le_one (D : Matrix ι κ ℂ) (hD : ‖D‖ ≤ 1) :
    (1 - D * Dᴴ).PosSemidef := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  have hp : (D * Dᴴ).PosSemidef := posSemidef_self_mul_conjTranspose D
  apply Matrix.nonneg_iff_posSemidef.mp
  apply sub_nonneg.mpr
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg (D * Dᴴ) hp.nonneg).mp
  calc
    ‖D * Dᴴ‖ ≤ ‖D‖ * ‖Dᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ = ‖D‖ * ‖D‖ := by rw [Matrix.l2_opNorm_conjTranspose]
    _ ≤ 1 := by nlinarith [norm_nonneg D]

theorem exists_positive_gram_splitting (F : Matrix ι κ ℂ)
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : (A + B - F * Fᴴ).PosSemidef) :
    ∃ F₀ F₁ : Matrix ι κ ℂ, F = F₀ + F₁ ∧
      (A - F₀ * F₀ᴴ).PosSemidef ∧ (B - F₁ * F₁ᴴ).PosSemidef := by
  let R := Pseudoinverse.root A hA
  let S := Pseudoinverse.root B hB
  have hR : Rᴴ = R := (Pseudoinverse.root_isHermitian A hA).eq
  have hS : Sᴴ = S := (Pseudoinverse.root_isHermitian B hB).eq
  have hRR : R * R = A := Pseudoinverse.root_mul_root A hA
  have hSS : S * S = B := Pseudoinverse.root_mul_root B hB
  let G := Matrix.fromCols R S
  have hG : G * Gᴴ = A + B := by
    simp only [G, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows, hR, hS, hRR, hSS]
  obtain ⟨D, hFD, hD⟩ := Factorization.matrix_factorization F G (t := 1) (by norm_num)
    (by simpa [hG] using h)
  have hpos := gram_le_one_of_norm_le_one D (by simpa using hD)
  let D₀ := D.submatrix Sum.inl id
  let D₁ := D.submatrix Sum.inr id
  have hparts : D = Matrix.fromRows D₀ D₁ := by ext (i | i) j <;> rfl
  have h₀ : (1 - D₀ * D₀ᴴ).PosSemidef := by
    have hh := hpos.submatrix Sum.inl
    convert hh using 1
    ext i j
    simp [D₀, Matrix.submatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have h₁ : (1 - D₁ * D₁ᴴ).PosSemidef := by
    have hh := hpos.submatrix Sum.inr
    convert hh using 1
    ext i j
    simp [D₁, Matrix.submatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  refine ⟨R * D₀, S * D₁, ?_, ?_, ?_⟩
  · rw [hFD, hparts]
    exact Matrix.fromCols_mul_fromRows R S D₀ D₁
  · have hh := h₀.mul_mul_conjTranspose_same R
    simpa only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.conjTranspose_mul, hR, Matrix.mul_assoc, hRR] using hh
  · have hh := h₁.mul_mul_conjTranspose_same S
    simpa only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.conjTranspose_mul, hS, Matrix.mul_assoc, hSS] using hh
end QuantumChannelStein
