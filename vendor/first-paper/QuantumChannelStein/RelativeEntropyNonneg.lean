import QuantumChannelStein.RelativeEntropy
import QuantumChannelStein.RelativeEntropyScalar

/-!
# Nonnegativity of finite-state Umegaki relative entropy

The proof uses the two states' actual spectral decompositions. Squared
eigenbasis overlaps form a doubly stochastic matrix, reducing Klein's
inequality to its scalar logarithmic form. Zero eigenvalues are handled
using the support condition rather than by assuming invertibility.
-/

noncomputable section
namespace QuantumChannelStein.RelativeEntropy

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

/-- Change of eigenbasis from the second state's basis to the first. -/
def eigenbasisChange (ρ σ : State n) : Matrix.unitaryGroup (Fin n) ℂ :=
  star ρ.positive.isHermitian.eigenvectorUnitary * σ.positive.isHermitian.eigenvectorUnitary

theorem eigenbasisChange_coe (ρ σ : State n) :
    (eigenbasisChange ρ σ : Operator n) =
      (ρ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
        (σ.positive.isHermitian.eigenvectorUnitary : Operator n) := rfl

/-- Squared absolute eigenbasis overlaps. -/
def overlapWeight (ρ σ : State n) (i j : Fin n) : ℝ :=
  Complex.normSq ((eigenbasisChange ρ σ : Operator n) i j)

theorem overlapWeight_nonneg (ρ σ : State n) (i j : Fin n) :
    0 ≤ overlapWeight ρ σ i j := Complex.normSq_nonneg _

/-- Unitarity makes each row of overlap weights a probability vector. -/
theorem sum_overlapWeight_row (ρ σ : State n) (i : Fin n) :
    ∑ j, overlapWeight ρ σ i j = 1 := by
  have h := congrArg (fun A : Operator n => (A i i).re)
    (unitary.coe_mul_star_self (eigenbasisChange ρ σ))
  simpa [overlapWeight, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Complex.mul_conj] using h

/-- Unitarity makes each column of overlap weights a probability vector. -/
theorem sum_overlapWeight_col (ρ σ : State n) (j : Fin n) :
    ∑ i, overlapWeight ρ σ i j = 1 := by
  have h := congrArg (fun A : Operator n => (A j j).re)
    (unitary.coe_star_mul_self (eigenbasisChange ρ σ))
  simpa [overlapWeight, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, ← Complex.normSq_eq_conj_mul_self] using h

/-- Trace one is the normalization of the state's nonnegative eigenvalues. -/
theorem sum_eigenvalues_eq_one (ρ : State n) :
    ∑ i, ρ.positive.isHermitian.eigenvalues i = 1 := by
  have h := congrArg Complex.re ρ.positive.isHermitian.trace_eq_sum_eigenvalues
  simpa [ρ.trace_one] using h.symm

/-- Express the first state in the second eigenbasis. -/
theorem eigenbasis_conjugation (ρ σ : State n) :
    (σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
      ρ.matrix * (σ.positive.isHermitian.eigenvectorUnitary : Operator n) =
    (eigenbasisChange ρ σ : Operator n)ᴴ *
      Matrix.diagonal (fun i => (ρ.positive.isHermitian.eigenvalues i : ℂ)) *
        (eigenbasisChange ρ σ : Operator n) := by
  conv_lhs =>
    arg 1
    arg 2
    rw [ρ.positive.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose]
  simp only [eigenbasisChange_coe, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rfl

/-- Diagonal weights in the second eigenbasis are the first eigenvalues
averaged against the squared eigenbasis overlaps. -/
theorem eigenbasis_weight_eq_sum (ρ σ : State n) (j : Fin n) :
    (((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
      ρ.matrix * (σ.positive.isHermitian.eigenvectorUnitary : Operator n)) j j).re =
        ∑ i, ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j := by
  rw [eigenbasis_conjugation]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Complex.re_sum, overlapWeight]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, mul_comm (ρ.positive.isHermitian.eigenvalues i : ℂ),
    ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp [mul_comm]

/-- Support inclusion removes exactly the terms where the first state
has positive weight but the second state has eigenvalue zero. -/
theorem eigenvalue_mul_overlap_eq_zero (ρ σ : State n)
    (h : supportIncluded ρ σ) (i j : Fin n)
    (hj : σ.positive.isHermitian.eigenvalues j = 0) :
    ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j = 0 := by
  have hsum : (∑ i, ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j) = 0 := by
    rw [← eigenbasis_weight_eq_sum]
    exact eigenbasis_weight_eq_zero_of_supportIncluded ρ σ h j hj
  have hnonneg (k : Fin n) :
      0 ≤ ρ.positive.isHermitian.eigenvalues k * overlapWeight ρ σ k j :=
    mul_nonneg (ρ.positive.eigenvalues_nonneg k) (overlapWeight_nonneg ρ σ k j)
  apply le_antisymm _ (hnonneg i)
  calc
    _ ≤ ∑ k, ρ.positive.isHermitian.eigenvalues k * overlapWeight ρ σ k j :=
      Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)
    _ = 0 := hsum

/-- The finite Umegaki trace is the doubly weighted classical logarithmic
expression determined by the two spectral decompositions. -/
theorem traceFormula_eq_overlap_sum (ρ σ : State n) :
    traceFormula ρ σ =
      ∑ i, ∑ j, overlapWeight ρ σ i j *
        (ρ.positive.isHermitian.eigenvalues i *
          (Real.logb 2 (ρ.positive.isHermitian.eigenvalues i) -
            Real.logb 2 (σ.positive.isHermitian.eigenvalues j))) := by
  rw [traceFormula_eq_spectral]
  simp_rw [eigenbasis_weight_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun j i =>
    ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j *
      Real.logb 2 (σ.positive.isHermitian.eigenvalues j))]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, sum_overlapWeight_row, one_mul]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Klein's inequality for the actual finite Umegaki trace expression.
The only domain condition is support inclusion; states may be singular. -/
theorem traceFormula_nonneg (ρ σ : State n) (h : supportIncluded ρ σ) :
    0 ≤ traceFormula ρ σ := by
  rw [traceFormula_eq_overlap_sum]
  exact doubly_stochastic_klein_log2
    ρ.positive.isHermitian.eigenvalues σ.positive.isHermitian.eigenvalues
    (overlapWeight ρ σ) ρ.positive.eigenvalues_nonneg σ.positive.eigenvalues_nonneg
    (sum_eigenvalues_eq_one ρ) (sum_eigenvalues_eq_one σ)
    (overlapWeight_nonneg ρ σ) (sum_overlapWeight_row ρ σ)
    (sum_overlapWeight_col ρ σ) (eigenvalue_mul_overlap_eq_zero ρ σ h)

/-- Finite-state Umegaki relative entropy is nonnegative, including its
infinite branch. -/
theorem umegaki_nonneg (ρ σ : State n) : 0 ≤ umegaki ρ σ := by
  classical
  by_cases h : supportIncluded ρ σ
  · rw [umegaki_of_supportIncluded ρ σ h, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    exact traceFormula_nonneg ρ σ h
  · rw [umegaki_of_not_supportIncluded ρ σ h]
    exact le_top

end QuantumChannelStein.RelativeEntropy
