import QuantumChannelStein.SharpDiagonalCalculus

noncomputable section
namespace QuantumChannelStein.SharpDiagonal
open Matrix SandwichedRenyi
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] matrixCStar
variable {n : ℕ}

theorem scalar_quasi_eq (α a b : ℝ) (hα : 1 < α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (b ^ sandwichExponent α * a * b ^ sandwichExponent α) ^ α =
      a ^ α * b ^ (1 - α) := by
  have hα0 : 0 < α := zero_lt_one.trans hα
  by_cases hb0 : b = 0
  · simp [hb0, Real.zero_rpow (sandwichExponent_neg hα).ne,
      Real.zero_rpow hα0.ne', Real.zero_rpow (show 1 - α ≠ 0 by linarith)]
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hs : (sandwichExponent α * α) + (sandwichExponent α * α) = 1 - α := by
    unfold sandwichExponent
    field_simp
    ring
  calc
    _ = (b ^ sandwichExponent α) ^ α * a ^ α * (b ^ sandwichExponent α) ^ α := by
      rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hb _) ha) (Real.rpow_nonneg hb _),
        Real.mul_rpow (Real.rpow_nonneg hb _) ha]
    _ = a ^ α * (b ^ (sandwichExponent α * α) * b ^ (sandwichExponent α * α)) := by
      rw [← Real.rpow_mul hb]
      ring
    _ = _ := by rw [← Real.rpow_add hbpos, hs]

theorem sandwiched_quasi_diagonal (α : ℝ) (hα : 1 < α) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    SandwichedRenyi.quasi α (diag a) (diag b) = ∑ i, a i ^ α * b i ^ (1 - α) := by
  let d := fun i => b i ^ sandwichExponent α * a i * b i ^ sandwichExponent α
  have hd : ∀ i, 0 ≤ d i := fun i =>
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (hb i) _) (ha i)) (Real.rpow_nonneg (hb i) _)
  have hS : sandwichedOperator α (diag a) (diag b) = diag d := by
    unfold sandwichedOperator
    rw [rpow_diag b hb, diag_mul, diag_mul]
  unfold SandwichedRenyi.quasi
  rw [hS, rpow_diag d hd]
  simp only [diag, Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
  apply Finset.sum_congr rfl
  intro i hi
  exact scalar_quasi_eq α (a i) (b i) hα (ha i) (hb i)

end QuantumChannelStein.SharpDiagonal
