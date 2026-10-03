import QuantumChannelStein.SandwichedQuasiBound

/-! # Support-aware quasi-divergence and the genuine Schatten-2 factor

`quasiExtended` restores positive infinity off support. `frobeniusNorm` is
explicitly the Euclidean norm of all matrix entries, equivalently the square
root of `Tr(F Fᴴ)`; it is not the L2 operator norm on matrices.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder
attribute [local instance] matrixCStar
variable {n m : ℕ}

/-- Extended quasi-divergence for PSD matrices and orders above one. -/
def quasiExtended (α : ℝ) (_hα : 1 < α) (A B : Operator n)
    (_hA : A.PosSemidef) (_hB : B.PosSemidef) : EReal := by
  classical
  exact if LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin then (quasi α A B : EReal) else ⊤

theorem quasiExtended_of_support (α : ℝ) (hα : 1 < α) (A B : Operator n)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    quasiExtended α hα A B hA hB = (quasi α A B : EReal) := by
  simp only [quasiExtended, if_pos hs]

theorem quasiExtended_of_not_support (α : ℝ) (hα : 1 < α) (A B : Operator n)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : ¬LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    quasiExtended α hα A B hA hB = ⊤ := by
  simp only [quasiExtended, if_neg hs]

/-- The first 3.8 bound in its genuinely support-aware extended codomain. -/
theorem quasiExtended_le_of_domination (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (A B : Operator n) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) (hdom : (t • B - A).PosSemidef) :
    quasiExtended α hα A B hA hB ≤ (t ^ (α - 1) * A.trace.re : ℝ) := by
  rw [quasiExtended_of_support _ _ _ _ _ _
    (SupportDomination.ker_le_of_posSemidef_smul_sub hA hdom)]
  exact EReal.coe_le_coe_iff.mpr (quasi_le_of_domination α hα hα2 A B hA hB t ht hdom)

/-- Squared Schatten-2/Frobenius norm, with no matrix operator norm involved. -/
def frobeniusSq (F : Matrix (Fin n) (Fin m) ℂ) : ℝ := (F * Fᴴ).trace.re

/-- Vectorization into the Hilbert space of all entries. -/
def frobeniusVector (F : Matrix (Fin n) (Fin m) ℂ) :
    EuclideanSpace ℂ (Fin n × Fin m) := WithLp.toLp 2 (fun p => F p.1 p.2)

def frobeniusNorm (F : Matrix (Fin n) (Fin m) ℂ) : ℝ := Real.sqrt (frobeniusSq F)

theorem frobeniusSq_eq_sum (F : Matrix (Fin n) (Fin m) ℂ) :
    frobeniusSq F = ∑ i, ∑ j, Complex.normSq (F i j) := by
  simp [frobeniusSq, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj]

theorem frobeniusSq_nonneg (F : Matrix (Fin n) (Fin m) ℂ) : 0 ≤ frobeniusSq F := by
  rw [frobeniusSq_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem frobeniusNorm_sq (F : Matrix (Fin n) (Fin m) ℂ) :
    frobeniusNorm F ^ 2 = (F * Fᴴ).trace.re :=
  Real.sq_sqrt (frobeniusSq_nonneg F)

theorem frobeniusSq_eq_vector_norm_sq (F : Matrix (Fin n) (Fin m) ℂ) :
    frobeniusSq F = ‖frobeniusVector F‖ ^ 2 := by
  rw [frobeniusSq_eq_sum, EuclideanSpace.norm_sq_eq]
  simp only [frobeniusVector, WithLp.ofLp_toLp, Fintype.sum_prod_type,
    Complex.normSq_eq_norm_sq]

theorem frobeniusNorm_eq_vector_norm (F : Matrix (Fin n) (Fin m) ℂ) :
    frobeniusNorm F = ‖frobeniusVector F‖ := by
  rw [frobeniusNorm, frobeniusSq_eq_vector_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The factor form uses the genuine Schatten-2 norm squared from the paper. -/
theorem quasi_factor_le_of_domination (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (F : Matrix (Fin n) (Fin m) ℂ) (B : Operator n) (hB : B.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) (hdom : (t • B - F * Fᴴ).PosSemidef) :
    quasi α (F * Fᴴ) B ≤ t ^ (α - 1) * frobeniusNorm F ^ 2 := by
  rw [frobeniusNorm_sq]
  have hF : (F * Fᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self Fᴴ
  exact quasi_le_of_domination α hα hα2 _ B hF hB t ht hdom

end QuantumChannelStein.SandwichedRenyi
