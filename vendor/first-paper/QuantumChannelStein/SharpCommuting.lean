import QuantumChannelStein.SharpDiagonalProgram
import QuantumChannelStein.CommutingQuasiFormula
import QuantumChannelStein.SandwichedUnitary

/-! # Exact commuting equality for the actual supported optimization
Simultaneous unitary diagonalization, actual diagonal pinching and a literal
feasible auxiliary prove both infimum inequalities. No optimization oracle
or invertibility assumption is present.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SharpDivergence
open Matrix SharpDiagonal
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] SandwichedRenyi.matrixCStar
variable {n : ℕ}

theorem isDiag_eq_real_diag (A : Operator n) (hA : A.PosSemidef) (hd : A.IsDiag) :
    A = SharpDiagonal.diag (fun i => (A i i).re) := by
  calc
    A = Matrix.diagonal A.diag := hd.diagonal_diag.symm
    _ = _ := by
      congr 1
      funext i
      apply Complex.ext
      · rfl
      · simpa only [Matrix.diag, Complex.ofReal_im] using
          (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).2.symm

theorem scalar_support_of_diag_support (a b : Fin n → ℝ)
    (h : LinearMap.ker (SharpDiagonal.diag b).mulVecLin ≤
      LinearMap.ker (SharpDiagonal.diag a).mulVecLin) :
    ∀ i, b i = 0 → a i = 0 := by
  intro i hi
  have hb : SharpDiagonal.diag b *ᵥ Pi.single i 1 = 0 := by
    ext j
    by_cases hj : j = i
    · subst j; simp [SharpDiagonal.diag, Matrix.mulVec_diagonal, hi]
    · simp [SharpDiagonal.diag, Matrix.mulVec_diagonal, Pi.single_apply, hj]
  have ha : SharpDiagonal.diag a *ᵥ Pi.single i 1 = 0 := h hb
  have hre := congrArg Complex.re (congrFun ha i)
  simpa [SharpDiagonal.diag, Matrix.mulVec_diagonal] using hre

/-- Exact classical/simultaneously diagonalizable value of the supported program. -/
theorem quasi_eq_sandwiched_of_commute (α : ℝ) (hα : 1 < α)
    (A B : Operator n) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) (hAB : Commute A B) :
    SharpDivergence.quasi (1 / α) A B hB = ENNReal.ofReal (SandwichedRenyi.quasi α A B) := by
  obtain ⟨U, hUdA, hUdB⟩ := Commute.exists_unitary_qcs hA.isHermitian hB.isHermitian hAB
  let a := fun i => (U.val * A * U.valᴴ) i i |>.re
  let b := fun i => (U.val * B * U.valᴴ) i i |>.re
  have hUA := hA.mul_mul_conjTranspose_same U.val
  have hUB := hB.mul_mul_conjTranspose_same U.val
  have ha : ∀ i, 0 ≤ a i := fun i => (Complex.nonneg_iff.mp (hUA.diag_nonneg (i := i))).1
  have hb : ∀ i, 0 ≤ b i := fun i => (Complex.nonneg_iff.mp (hUB.diag_nonneg (i := i))).1
  have heA : U.val * A * U.valᴴ = SharpDiagonal.diag a := isDiag_eq_real_diag _ hUA hUdA
  have heB : U.val * B * U.valᴴ = SharpDiagonal.diag b := isDiag_eq_real_diag _ hUB hUdB
  have hsup : LinearMap.ker (U.val * B * U.valᴴ).mulVecLin ≤
      LinearMap.ker (U.val * A * U.valᴴ).mulVecLin := by
    simpa [SupportedGeometricMean.krausSum] using
      SupportedGeometricMean.krausSum_support ({()} : Finset Unit) (fun _ => U.val) A B hA hB hs
  rw [heA, heB] at hsup
  have hab := scalar_support_of_diag_support a b hsup
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hp : 1 / α ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨one_div_pos.mpr hα0, (div_le_one hα0).mpr hα.le⟩
  calc
    SharpDivergence.quasi (1 / α) A B hB =
        SharpDivergence.quasi (1 / α) (U.val * A * U.valᴴ) (U.val * B * U.valᴴ) hUB :=
      (SharpDivergence.quasi_unitary (1 / α) hp U A B hB).symm
    _ = SharpDivergence.quasi (1 / α) (SharpDiagonal.diag a) (SharpDiagonal.diag b) (diag_positive b hb) :=
      quasi_congr (1 / α) hUB (diag_positive b hb) heA heB
    _ = ENNReal.ofReal (∑ i, a i ^ α * b i ^ (1 - α)) := sharp_quasi_diagonal α hα a b ha hb hab
    _ = ENNReal.ofReal (SandwichedRenyi.quasi α (SharpDiagonal.diag a) (SharpDiagonal.diag b)) := by
      rw [sandwiched_quasi_diagonal α hα a b ha hb]
    _ = ENNReal.ofReal (SandwichedRenyi.quasi α (U.val * A * U.valᴴ) (U.val * B * U.valᴴ)) := by
      rw [heA, heB]
    _ = _ := congrArg ENNReal.ofReal (SandwichedRenyi.quasi_unitary α U A B hA hB)

end QuantumChannelStein.SharpDivergence
