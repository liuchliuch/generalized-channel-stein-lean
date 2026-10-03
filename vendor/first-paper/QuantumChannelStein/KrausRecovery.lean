import QuantumChannelStein.SandwichedRenyiBridge
import QuantumChannelStein.PositiveSplitting

/-! # Actual trace-preserving completion of a rectangular contraction

The first Kraus operator is the prescribed contraction. The remaining
operators send its positive trace defect to one fixed output basis vector.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.KrausRecovery
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n r : ℕ}

def rowKraus (R : Operator n) (z : Fin r) (i : Fin n) : Matrix (Fin r) (Fin n) ℂ :=
  fun a b => if a = z then R i b else 0

theorem sum_rowKraus_gram (R : Operator n) (z : Fin r) :
    ∑ i : Fin n, (rowKraus R z i)ᴴ * rowKraus R z i = Rᴴ * R := by
  ext i j
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, rowKraus]

def defect (A : Matrix (Fin r) (Fin n) ℂ) : Operator n := 1 - Aᴴ * A

theorem defect_positive (A : Matrix (Fin r) (Fin n) ℂ) (hA : ‖A‖ ≤ 1) :
    (defect A).PosSemidef := by
  simpa only [defect, Matrix.conjTranspose_conjTranspose] using
    gram_le_one_of_norm_le_one Aᴴ (by simpa only [Matrix.l2_opNorm_conjTranspose] using hA)

def channel (A : Matrix (Fin r) (Fin n) ℂ) (hA : ‖A‖ ≤ 1) (z : Fin r) : KrausChannel n r where
  rank := 1 + n
  kraus := Fin.addCases (fun _ : Fin 1 => A) (rowKraus (CFC.sqrt (defect A)) z)
  normalized := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_one, sum_rowKraus_gram]
    have hroot : (CFC.sqrt (defect A)).IsHermitian := CFC.sqrt_nonneg (defect A) |>.posSemidef.isHermitian
    rw [hroot.eq, CFC.sqrt_mul_sqrt_self _ (defect_positive A hA).nonneg]
    simp only [defect]
    abel

theorem channel_apply (A : Matrix (Fin r) (Fin n) ℂ) (hA : ‖A‖ ≤ 1) (z : Fin r) (X : Operator n) :
    (channel A hA z).apply X = A * X * Aᴴ +
      ∑ i : Fin n, rowKraus (CFC.sqrt (defect A)) z i * X *
        (rowKraus (CFC.sqrt (defect A)) z i)ᴴ := by
  unfold KrausChannel.apply channel
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_one]

theorem channel_dominates_contraction (A : Matrix (Fin r) (Fin n) ℂ) (hA : ‖A‖ ≤ 1)
    (z : Fin r) (X : Operator n) (hX : X.PosSemidef) :
    ((channel A hA z).apply X - A * X * Aᴴ).PosSemidef := by
  rw [channel_apply, add_sub_cancel_left]
  apply Finset.sum_induction
  · intro B C hB hC
    exact hB.add hC
  · exact Matrix.PosSemidef.zero
  · intro i _
    exact hX.mul_mul_conjTranspose_same _

/-- A PSD remainder with zero trace is zero, so domination at equal trace is equality. -/
theorem eq_of_domination_trace_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (h : (B - A).PosSemidef) (htr : B.trace = A.trace) : B = A := by
  have ht : (B - A).trace = 0 := by rw [Matrix.trace_sub, htr, sub_self]
  exact sub_eq_zero.mp (h.trace_eq_zero_iff.mp ht)

end QuantumChannelStein.KrausRecovery
