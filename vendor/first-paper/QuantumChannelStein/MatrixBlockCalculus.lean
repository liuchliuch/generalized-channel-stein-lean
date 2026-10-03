import QuantumChannelStein.SupportedGeometricMean

/-! # Direct sums in finite-matrix functional calculus
A concrete block-diagonal star homomorphism transports arbitrary spectral
functions, including the discontinuous inverse square root at zero.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QuantumChannelStein.MatrixBlockCalculus
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def blockHom : (Matrix ι ι ℂ × Matrix κ κ ℂ) →⋆ₐ[ℂ] Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ where
  toFun AB := fromBlocks AB.1 0 0 AB.2
  map_zero' := by ext i j <;> cases i <;> cases j <;> rfl
  map_one' := by ext i j <;> cases i <;> cases j <;> simp [Matrix.one_apply]
  map_add' A B := by ext i j <;> cases i <;> cases j <;> simp
  map_mul' A B := by simp [fromBlocks_multiply]
  commutes' c := by ext i j <;> cases i <;> cases j <;> simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  map_star' A := by simp [Matrix.star_eq_conjTranspose, fromBlocks_conjTranspose]

variable {ι κ}
local instance matrixBlockCalculusCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
local instance matrixBlockCalculusCStar2 : CStarAlgebra (Matrix κ κ ℂ) := CStarAlgebra.mk
local instance matrixBlockCalculusCStar3 : CStarAlgebra (Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) := CStarAlgebra.mk

theorem cfc_fromBlocks (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    cfc f (fromBlocks A 0 0 B) = fromBlocks (cfc f A) 0 0 (cfc f B) := by
  have hf : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B) :=
    (A.finite_real_spectrum.union B.finite_real_spectrum).continuousOn f
  have hAB : IsSelfAdjoint (A, B) := Prod.ext hA.eq hB.eq
  have hφ : Continuous (blockHom ι κ) := by
    change Continuous (fun AB : Matrix ι ι ℂ × Matrix κ κ ℂ => fromBlocks AB.1 0 0 AB.2)
    fun_prop
  have h := (blockHom ι κ).map_cfc f (A, B) (by simpa only [Prod.spectrum_eq] using hf)
    hφ hAB (hAB.map (blockHom ι κ))
  rw [cfc_map_prod (S := ℂ) f A B hf hAB hA.isSelfAdjoint hB.isSelfAdjoint] at h
  exact h.symm

theorem fromBlocks_positive (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (fromBlocks A 0 0 B).PosSemidef := by
  have h : (0 : Matrix ι ι ℂ × Matrix κ κ ℂ) ≤ (A, B) := ⟨hA.nonneg, hB.nonneg⟩
  have hm := OrderHomClass.mono (blockHom ι κ) h
  have hh : 0 ≤ (blockHom ι κ) (A, B) := by simpa only [map_zero] using hm
  exact hh.posSemidef

theorem root_fromBlocks (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Pseudoinverse.root (fromBlocks A 0 0 B) (fromBlocks_positive A B hA hB) =
      fromBlocks (Pseudoinverse.root A hA) 0 0 (Pseudoinverse.root B hB) := by
  unfold Pseudoinverse.root
  rw [← (fromBlocks_positive A B hA hB).isHermitian.cfc_eq,
    ← hA.isHermitian.cfc_eq, ← hB.isHermitian.cfc_eq]
  exact cfc_fromBlocks A B hA.isHermitian hB.isHermitian Real.sqrt

theorem inverseSqrt_fromBlocks (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Pseudoinverse.inverseSqrt (fromBlocks A 0 0 B) (fromBlocks_positive A B hA hB) =
      fromBlocks (Pseudoinverse.inverseSqrt A hA) 0 0 (Pseudoinverse.inverseSqrt B hB) := by
  unfold Pseudoinverse.inverseSqrt
  rw [← (fromBlocks_positive A B hA hB).isHermitian.cfc_eq,
    ← hA.isHermitian.cfc_eq, ← hB.isHermitian.cfc_eq]
  exact cfc_fromBlocks A B hA.isHermitian hB.isHermitian (fun x => (Real.sqrt x)⁻¹)

theorem rpow_fromBlocks (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (p : ℝ) :
    CFC.rpow (fromBlocks A 0 0 B) p = fromBlocks (CFC.rpow A p) 0 0 (CFC.rpow B p) := by
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA.nonneg,
    CFC.rpow_eq_cfc_real hB.nonneg,
    CFC.rpow_eq_cfc_real (fromBlocks_positive A B hA hB).nonneg]
  exact cfc_fromBlocks A B hA.isHermitian hB.isHermitian (fun x => x ^ p)

end QuantumChannelStein.MatrixBlockCalculus
