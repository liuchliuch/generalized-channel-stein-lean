import QuantumChannelStein.RectangularPowerCompression

/-! # Support projections for rectangular Gram factors
All formulas retain the zero eigenspaces. Douglas factorization is used to
transport a support projection to an arbitrary rectangular Gram factor.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.Pseudoinverse
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
local instance pseudoinverseSupportCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk

private theorem spectral_mul' (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) : hB.cfc f * hB.cfc g = hB.cfc (fun x => f x * g x) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_mul]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij, Function.comp_def]

theorem supportProjection_norm_le_one (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    ‖supportProjection B hB‖ ≤ 1 := by
  unfold supportProjection
  rw [← hB.isHermitian.cfc_eq]
  apply norm_cfc_le zero_le_one
  intro x hx
  split_ifs <;> simp

theorem supportProjection_mul_root (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    supportProjection B hB * root B hB = root B hB := by
  unfold supportProjection root
  rw [spectral_mul']
  congr 1
  funext x
  by_cases hx : x = 0 <;> simp [hx]

theorem root_mul_supportProjection (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    root B hB * supportProjection B hB = root B hB := by
  have h := congrArg Matrix.conjTranspose (supportProjection_mul_root B hB)
  simpa only [Matrix.conjTranspose_mul, (root_isHermitian B hB).eq,
    (supportProjection_isHermitian B hB).eq] using h

/-- The support of a rectangular Gram matrix contains every column of its factor. -/
theorem supportProjection_gram_mul (F : Matrix ι κ ℂ) :
    supportProjection (F * Fᴴ) (posSemidef_self_mul_conjTranspose F) * F = F := by
  let hB := posSemidef_self_mul_conjTranspose F
  obtain ⟨D, hD, _⟩ := Factorization.matrix_factorization F (root (F * Fᴴ) hB)
    (t := 1) zero_le_one (by
      rw [(root_isHermitian _ hB).eq, root_mul_root]
      simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef))
  calc
    _ = supportProjection (F * Fᴴ) hB * (root (F * Fᴴ) hB * D) := congrArg (fun Z => supportProjection (F * Fᴴ) hB * Z) hD
    _ = root (F * Fᴴ) hB * D := by rw [← Matrix.mul_assoc, supportProjection_mul_root]
    _ = F := hD.symm

/-- Canonical normalized rectangular factor, with its actual norm bound. -/
theorem inverseSqrt_gram_mul_norm_le_one (F : Matrix ι κ ℂ) :
    ‖inverseSqrt (F * Fᴴ) (posSemidef_self_mul_conjTranspose F) * F‖ ≤ 1 := by
  let hB := posSemidef_self_mul_conjTranspose F
  obtain ⟨D, hD, hn⟩ := Factorization.matrix_factorization F (root (F * Fᴴ) hB)
    (t := 1) zero_le_one (by
      rw [(root_isHermitian _ hB).eq, root_mul_root]
      simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef))
  have heq : inverseSqrt (F * Fᴴ) hB * F = supportProjection (F * Fᴴ) hB * D := by
    calc
      _ = inverseSqrt (F * Fᴴ) hB * (root (F * Fᴴ) hB * D) := congrArg (fun Z => inverseSqrt (F * Fᴴ) hB * Z) hD
      _ = _ := by rw [← Matrix.mul_assoc, inverseSqrt_mul_root]
  rw [heq]
  calc
    _ ≤ ‖supportProjection (F * Fᴴ) hB‖ * ‖D‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * 1 := mul_le_mul (supportProjection_norm_le_one _ hB)
      (by simpa using hn) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem inverseSqrt_mul_norm_of_gram (F : Matrix ι κ ℂ)
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (heq : F * Fᴴ = B) :
    ‖inverseSqrt B hB * F‖ ≤ 1 := by
  subst B
  exact inverseSqrt_gram_mul_norm_le_one F

theorem supportProjection_mul_of_gram (F : Matrix ι κ ℂ)
    (B : Matrix ι ι ℂ) (hB : B.PosSemidef) (heq : F * Fᴴ = B) :
    supportProjection B hB * F = F := by
  subst B
  exact supportProjection_gram_mul F

end QuantumChannelStein.Pseudoinverse
