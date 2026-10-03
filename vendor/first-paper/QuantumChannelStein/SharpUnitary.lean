import QuantumChannelStein.SharpDataProcessing
import QuantumChannelStein.GeometricMeanCongruence
import QuantumChannelStein.SimultaneousDiagonalization

/-! # Concrete unitary changes of basis and diagonal pinching for the program -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SharpDivergence
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] SandwichedRenyi.matrixCStar
variable {n : ℕ}

def unitaryChannel (U : Matrix.unitaryGroup (Fin n) ℂ) : KrausChannel n n where
  rank := 1
  kraus := fun _ => U.val
  normalized := by simpa only [Fin.sum_univ_one, ← Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U

theorem unitaryChannel_apply (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Operator n) :
    (unitaryChannel U).apply X = U.val * X * U.valᴴ := by
  simp [KrausChannel.apply, unitaryChannel]

theorem quasi_congr (p : ℝ) {A B C D : Operator n} (hB : B.PosSemidef) (hD : D.PosSemidef)
    (hAC : A = C) (hBD : B = D) : quasi p A B hB = quasi p C D hD := by
  subst C
  subst D
  rfl

theorem quasi_unitary (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (A B : Operator n) (hB : B.PosSemidef) :
    quasi p (U.val * A * U.valᴴ) (U.val * B * U.valᴴ) (hB.mul_mul_conjTranspose_same U.val) =
      quasi p A B hB := by
  have hforward := quasi_data_processing p hp (unitaryChannel U) A B hB
  have heq := quasi_congr p ((unitaryChannel U).apply_positive hB)
    (hB.mul_mul_conjTranspose_same U.val) (unitaryChannel_apply U A) (unitaryChannel_apply U B)
  rw [heq] at hforward
  apply le_antisymm hforward
  have hback := quasi_data_processing p hp (unitaryChannel (star U))
    (U.val * A * U.valᴴ) (U.val * B * U.valᴴ) (hB.mul_mul_conjTranspose_same U.val)
  have hundo (X : Operator n) : (unitaryChannel (star U)).apply (U.val * X * U.valᴴ) = X := by
    rw [unitaryChannel_apply]
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      SupportedGeometricMean.undo_congruence U.val U.valᴴ X
        (by simpa only [← Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U)
  have heq' := quasi_congr p ((unitaryChannel (star U)).apply_positive
    (hB.mul_mul_conjTranspose_same U.val)) hB (hundo A) (hundo B)
  rw [heq'] at hback
  exact hback

/-- Actual complete dephasing channel in the computational orthonormal basis. -/
def diagonalChannel (n : ℕ) : KrausChannel n n where
  rank := n
  kraus k i j := if i = k ∧ j = k then 1 else 0
  normalized := by
    ext i j
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, ite_and, apply_ite, eq_comm]

theorem diagonalChannel_apply (X : Operator n) :
    (diagonalChannel n).apply X = Matrix.diagonal X.diag := by
  ext i j
  simp [KrausChannel.apply, diagonalChannel, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.diag, ite_and, apply_ite, eq_comm]
  split_ifs <;> simp_all

end QuantumChannelStein.SharpDivergence
