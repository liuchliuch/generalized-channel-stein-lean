import QuantumChannelStein.Choi
import Mathlib.Analysis.Matrix.Order

/-!
# The converse finite-dimensional Choi criterion

A positive semidefinite input-first Choi matrix whose output partial trace is the
identity has a normalized finite Kraus representation.
-/
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace KrausChannel
variable {n m r : ℕ}

/-- Reshape a family of vectorized Kraus columns into a normalized channel. -/
def ofColumns (V : Matrix (Fin n × Fin m) (Fin r) ℂ)
    (hV : traceOutput (V * Vᴴ) = 1) : KrausChannel n m where
  rank := r
  kraus k a i := V (i, a) k
  normalized := by
    ext i j
    have h := congrFun (congrFun hV j) i
    simp only [traceOutput, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    simpa only [mul_comm, Matrix.one_apply, eq_comm] using h

@[simp] theorem ofColumns_krausColumns
    (V : Matrix (Fin n × Fin m) (Fin r) ℂ)
    (hV : traceOutput (V * Vᴴ) = 1) :
    (ofColumns V hV).krausColumns = V := rfl

/-- Reshaping columns recovers their Gram matrix exactly. -/
@[simp] theorem choi_ofColumns
    (V : Matrix (Fin n × Fin m) (Fin r) ℂ)
    (hV : traceOutput (V * Vᴴ) = 1) :
    (ofColumns V hV).choi = V * Vᴴ := by
  rw [choi_eq_columns, ofColumns_krausColumns]

/-- A PSD matrix admits a finite column Gram representation with at most `n*m`
columns (zero columns are allowed). -/
theorem exists_columns_of_positive
    (J : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)
    (hJ : J.PosSemidef) :
    ∃ V : Matrix (Fin n × Fin m) (Fin (n * m)) ℂ, J = V * Vᴴ := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hJ.nonneg
  let V : Matrix (Fin n × Fin m) (Fin (n * m)) ℂ :=
    fun x k => Bᴴ x (finProdFinEquiv.symm k)
  refine ⟨V, hB.trans ?_⟩
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, star_star]
  exact (finProdFinEquiv.symm.sum_comp (fun k => star (B k x) * B k y)).symm

/-- The concrete converse Choi theorem: every PSD input-first matrix with output
marginal equal to the identity is the Choi matrix of a normalized Kraus channel.
The construction uses no more than the input-output dimension in Kraus slots. -/
theorem exists_of_choi
    (J : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)
    (hJ : J.PosSemidef) (htr : traceOutput J = 1) :
    ∃ Φ : KrausChannel n m, Φ.rank = n * m ∧ Φ.choi = J := by
  obtain ⟨V, hV⟩ := exists_columns_of_positive J hJ
  have hnorm : traceOutput (V * Vᴴ) = 1 := hV ▸ htr
  exact ⟨ofColumns V hnorm, rfl, (choi_ofColumns V hnorm).trans hV.symm⟩

/-- Positivity and the output marginal exactly characterize concrete Choi
matrices of finite normalized Kraus channels. -/
theorem is_choi_iff
    (J : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    (∃ Φ : KrausChannel n m, Φ.choi = J) ↔
      J.PosSemidef ∧ traceOutput J = 1 := by
  constructor
  · rintro ⟨Φ, rfl⟩
    exact ⟨Φ.choi_positive, Φ.traceOutput_choi⟩
  · rintro ⟨hJ, htr⟩
    obtain ⟨Φ, _, hΦ⟩ := exists_of_choi J hJ htr
    exact ⟨Φ, hΦ⟩

end KrausChannel
end QuantumChannelStein
