import QuantumChannelStein.SandwichedQuasiBound

noncomputable section
namespace QuantumChannelStein.SandwichedRenyi
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] matrixCStar
variable {n : ℕ}

theorem quasi_smul_first (α c : ℝ) (hc : 0 ≤ c) (A B : Operator n) (hA : A.PosSemidef) :
    quasi α (c • A) B = c ^ α * quasi α A B := by
  have hs : sandwichedOperator α (c • A) B = c • sandwichedOperator α A B := by
    simp only [sandwichedOperator, Matrix.mul_smul, Matrix.smul_mul]
  unfold quasi
  rw [hs, rpow_real_smul _ (sandwichedOperator_positive α hA) c α hc, Matrix.trace_smul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end QuantumChannelStein.SandwichedRenyi
