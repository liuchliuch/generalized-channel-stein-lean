import QuantumChannelStein.PowerCompression
import QuantumChannelStein.PositiveSplitting
import Mathlib.Data.Matrix.Block

/-! # Zero-padding and continuous functional calculus
Nonunital corner embeddings retain genuine positive powers, including their
zero eigenspaces. This permits rectangular compression without dimension
restrictions or an invertibility assumption.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QuantumChannelStein.MatrixCornerCalculus
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The upper-left zero-padded corner, as a genuine nonunital star homomorphism. -/
def cornerHom : Matrix ι ι ℂ →⋆ₙₐ[ℂ] Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ where
  toFun A := fromBlocks A 0 0 0
  map_zero' := by ext i j <;> cases i <;> cases j <;> rfl
  map_add' A B := by ext i j <;> cases i <;> cases j <;> simp
  map_mul' A B := by simp [fromBlocks_multiply]
  map_smul' c A := by ext i j <;> cases i <;> cases j <;> simp
  map_star' A := by simp [Matrix.star_eq_conjTranspose, fromBlocks_conjTranspose]

variable {ι κ}
local instance matrixCornerCalculusCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
local instance matrixCornerCalculusCStar2 : CStarAlgebra (Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ) := CStarAlgebra.mk

theorem corner_nonneg {A : Matrix ι ι ℂ} (hA : 0 ≤ A) :
    0 ≤ cornerHom ι κ A := by
  simpa using OrderHomClass.mono (cornerHom ι κ) hA

theorem corner_rpow (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (p : ℝ) (hp : 0 < p) :
    cornerHom ι κ (CFC.rpow A p) = CFC.rpow (cornerHom ι κ A) p := by
  have hφ : Continuous (cornerHom ι κ) := by
    change Continuous (fun A : Matrix ι ι ℂ => fromBlocks A 0 0 0)
    fun_prop
  have hf : Continuous (fun x : ℝ => x ^ p) := Real.continuous_rpow_const hp.le
  have hf0 : (0 : ℝ) ^ p = 0 := Real.zero_rpow hp.ne'
  have hc := (cornerHom ι κ).map_cfcₙ (fun x : ℝ => x ^ p) A
    hf.continuousOn hf0 hφ hA.isHermitian.isSelfAdjoint
    (hA.isHermitian.isSelfAdjoint.map (cornerHom ι κ))
  simp only [cfcₙ_eq_cfc hf.continuousOn hf0] at hc
  simpa only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA.nonneg,
    CFC.rpow_eq_cfc_real (corner_nonneg (κ := κ) hA.nonneg)] using hc

end QuantumChannelStein.MatrixCornerCalculus
