import QuantumChannelStein.Testing

/-! # A binary effect as an actual trace-preserving Kraus channel -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.BinaryMeasurement
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

def complement {n : ℕ} (T : Effect n) : Effect n :=
  ⟨1 - T.matrix, T.complement_positive, by simpa using T.positive⟩

def rowKraus {n : ℕ} (R : Operator n) (z : Fin 2) (i : Fin n) :
    Matrix (Fin 2) (Fin n) ℂ := fun a b => if a = z then R i b else 0

theorem sum_rowKraus_gram {n : ℕ} (R : Operator n) (z : Fin 2) :
    ∑ i : Fin n, (rowKraus R z i)ᴴ * rowKraus R z i = Rᴴ * R := by
  ext i j
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]

theorem sum_rowKraus_action {n : ℕ} (R X : Operator n) (z : Fin 2) :
    ∑ i : Fin n, rowKraus R z i * X * (rowKraus R z i)ᴴ =
      Matrix.diagonal (fun a : Fin 2 => if a = z then (R * X * Rᴴ).trace else 0) := by
  ext a b
  fin_cases a <;> fin_cases b <;> fin_cases z <;>
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus, Matrix.trace]

def channel {n : ℕ} (T : Effect n) : KrausChannel n 2 where
  rank := n + n
  kraus := Fin.addCases (rowKraus T.sqrtMatrix 0) (rowKraus (complement T).sqrtMatrix 1)
  normalized := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, sum_rowKraus_gram,
      T.sqrtMatrix_positive.isHermitian.eq, (complement T).sqrtMatrix_positive.isHermitian.eq,
      T.sqrtMatrix_mul_self, (complement T).sqrtMatrix_mul_self]
    change T.matrix + (1 - T.matrix) = 1
    abel

theorem channel_apply {n : ℕ} (T : Effect n) (X : Operator n) :
    (channel T).apply X = Matrix.diagonal ![(T.matrix * X).trace, ((1 - T.matrix) * X).trace] := by
  unfold KrausChannel.apply channel
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, sum_rowKraus_action]
  have h₀ : (T.sqrtMatrix * X * T.sqrtMatrixᴴ).trace = (T.matrix * X).trace := by
    rw [Matrix.trace_mul_cycle, T.sqrtMatrix_positive.isHermitian.eq, T.sqrtMatrix_mul_self]
  have h₁ : ((complement T).sqrtMatrix * X * (complement T).sqrtMatrixᴴ).trace =
      ((1 - T.matrix) * X).trace := by
    rw [Matrix.trace_mul_cycle, (complement T).sqrtMatrix_positive.isHermitian.eq,
      (complement T).sqrtMatrix_mul_self]
    rfl
  rw [h₀, h₁, Matrix.diagonal_add]
  congr 1
  ext i
  fin_cases i <;> simp
end QuantumChannelStein.BinaryMeasurement
