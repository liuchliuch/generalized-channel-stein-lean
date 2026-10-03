import QuantumChannelStein.Kraus

/-!
# Choi matrices for concrete Kraus channels

The input-first, unnormalized Choi convention of §3.1 of arXiv:2609.27196.
These results establish positivity and the partial-trace normalization for a
Kraus-presented channel. The converse Choi criterion is not asserted here.
-/
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder
open Matrix
namespace KrausChannel
variable {n m : ℕ}

/-- Input-first, unnormalized Choi matrix. -/
def choi (Φ : KrausChannel n m) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  fun x y => Φ.apply (Matrix.single x.1 y.1 1) x.2 y.2

/-- Each column is one vectorized Kraus operator, input index first. -/
def krausColumns (Φ : KrausChannel n m) :
    Matrix (Fin n × Fin m) (Fin Φ.rank) ℂ :=
  fun x i => Φ.kraus i x.2 x.1

/-- The concrete Choi matrix is the Gram matrix of Kraus columns. -/
theorem choi_eq_columns (Φ : KrausChannel n m) :
    Φ.choi = Φ.krausColumns * Φ.krausColumnsᴴ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [choi, apply, krausColumns, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single, ite_and]

/-- The Choi matrix of a Kraus channel is positive semidefinite. -/
theorem choi_positive (Φ : KrausChannel n m) : Φ.choi.PosSemidef := by
  rw [Φ.choi_eq_columns]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Partial trace over the output factor. -/
def traceOutput (X : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) : Operator n :=
  fun i j => ∑ a, X (i, a) (j, a)

/-- Trace preservation gives the unnormalized Choi marginal identity. -/
theorem traceOutput_choi (Φ : KrausChannel n m) : traceOutput Φ.choi = 1 := by
  ext i j
  have h := congrFun (congrFun Φ.normalized j) i
  rw [Φ.choi_eq_columns]
  simp only [traceOutput, krausColumns, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply] at h ⊢
  rw [Finset.sum_comm]
  simpa only [mul_comm, Matrix.one_apply, eq_comm] using h

end KrausChannel
end QuantumChannelStein
