import QuantumChannelStein.SandwichedRenyiTensor
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-! # A finite spectral lower bound for the actual sandwiched quasi-divergence

This file uses only scalar Jensen, the proved matrix spectral theorem,
and equality of the characteristic polynomials of the two Gram matrices.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix RelativeEntropy SpectralDecomposition
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] matrixCStar
variable {n : ℕ}

theorem unitary_sum_row_normSq (U : Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ j, Complex.normSq ((U : Operator n) i j) = 1 := by
  have h := congrArg (fun A : Operator n => (A i i).re) (Unitary.coe_mul_star_self U)
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Complex.mul_conj] using h

theorem unitary_sum_col_normSq (U : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i, Complex.normSq ((U : Operator n) i j) = 1 := by
  have h := congrArg (fun A : Operator n => (A j j).re) (Unitary.coe_star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    ← Complex.normSq_eq_conj_mul_self] using h

theorem unitary_diagonal_entry (U : Matrix.unitaryGroup (Fin n) ℂ) (d : Fin n → ℝ) (i : Fin n) :
    (((U : Operator n) * diagonal (fun j => (d j : ℂ)) * (U : Operator n)ᴴ) i i).re =
      ∑ j, Complex.normSq ((U : Operator n) i j) * d j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_right_comm, Complex.star_def, Complex.mul_conj]
  simp

theorem matrix_rpow_trace (A : Operator n) (hA : A.PosSemidef) (p : ℝ) :
    (CFC.rpow A p).trace.re = ∑ i, hA.isHermitian.eigenvalues i ^ p := by
  have hs : A = (hA.isHermitian.eigenvectorUnitary : Operator n) *
      diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) *
      (hA.isHermitian.eigenvectorUnitary : Operator n)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      using hA.isHermitian.spectral_theorem
  have hc := cfc_of_unitary_diagonalization hA.isHermitian.eigenvectorUnitary
    hA.isHermitian.eigenvalues (fun x : ℝ => x ^ p)
  rw [← hs] at hc
  rw [matrix_rpow_eq_cfc A hA, hc]
  have hu : (hA.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
      (hA.isHermitian.eigenvectorUnitary : Operator n) = 1 := Unitary.coe_star_mul_self _
  rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]

/-- Scalar convexity in the actual eigenbasis gives the diagonal-power lower bound. -/
theorem sum_diagonal_rpow_le_trace (A : Operator n) (hA : A.PosSemidef)
    (α : ℝ) (hα : 1 ≤ α) :
    ∑ i, (A i i).re ^ α ≤ (CFC.rpow A α).trace.re := by
  let U := hA.isHermitian.eigenvectorUnitary
  let eig := hA.isHermitian.eigenvalues
  have hdiag (i : Fin n) : (A i i).re = ∑ j, Complex.normSq ((U : Operator n) i j) * eig j := by
    have hs := hA.isHermitian.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at hs
    conv_lhs => rw [hs]
    exact unitary_diagonal_entry U eig i
  have hJ (i : Fin n) : (A i i).re ^ α ≤ ∑ j, Complex.normSq ((U : Operator n) i j) * (eig j ^ α) := by
    rw [hdiag]
    simpa only [smul_eq_mul] using (convexOn_rpow hα).map_sum_le
      (t := Finset.univ) (w := fun j => Complex.normSq ((U : Operator n) i j))
      (p := eig) (fun j _ => Complex.normSq_nonneg _) (unitary_sum_row_normSq U i)
      (fun j _ => hA.eigenvalues_nonneg j)
  calc
    _ ≤ ∑ i, ∑ j, Complex.normSq ((U : Operator n) i j) * (eig j ^ α) :=
      Finset.sum_le_sum (fun i _ => hJ i)
    _ = ∑ j, eig j ^ α := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, unitary_sum_col_normSq, one_mul]
    _ = _ := (matrix_rpow_trace A hA α).symm

/-- Both square Gram matrices have exactly the same ordered eigenvalue list,
including all zero eigenvalues, so every real power has the same trace. -/
theorem trace_rpow_gram_swap (C : Operator n) (p : ℝ) :
    (CFC.rpow (C * Cᴴ) p).trace.re = (CFC.rpow (Cᴴ * C) p).trace.re := by
  have hA := Matrix.posSemidef_self_mul_conjTranspose C
  have hB := Matrix.posSemidef_conjTranspose_mul_self C
  have he : hA.isHermitian.eigenvalues = hB.isHermitian.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact Matrix.charpoly_mul_comm C Cᴴ
  rw [matrix_rpow_trace _ hA, matrix_rpow_trace _ hB, he]

/-- The spectral Gram factor turns the sandwiched quasi-divergence into the
power trace of a Gram matrix whose diagonal is evaluated below. -/
theorem quasi_eq_spectralFactor_gram (α : ℝ) (ρ σ : State n) :
    quasi α ρ.matrix σ.matrix =
      (CFC.rpow ((CFC.rpow σ.matrix (sandwichExponent α) * spectralFactor ρ)ᴴ *
        (CFC.rpow σ.matrix (sandwichExponent α) * spectralFactor ρ)) α).trace.re := by
  let P := CFC.rpow σ.matrix (sandwichExponent α)
  have hP : P.IsHermitian := CFC.rpow_nonneg.posSemidef.isHermitian
  have he : (P * spectralFactor ρ) * (P * spectralFactor ρ)ᴴ = sandwichedOperator α ρ.matrix σ.matrix := by
    rw [Matrix.conjTranspose_mul, hP.eq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (spectralFactor ρ), spectralFactor_mul_conjTranspose]
    simp only [sandwichedOperator, P, Matrix.mul_assoc]
  unfold quasi
  rw [← he, trace_rpow_gram_swap]

/-- Exact diagonal of the reversed Gram matrix in the rho eigenbasis. -/
theorem spectralFactor_gram_diagonal (α : ℝ) (hα : 1 < α) (ρ σ : State n) (i : Fin n) :
    (((CFC.rpow σ.matrix (sandwichExponent α) * spectralFactor ρ)ᴴ *
      (CFC.rpow σ.matrix (sandwichExponent α) * spectralFactor ρ)) i i).re =
    ρ.positive.isHermitian.eigenvalues i *
      ∑ j, overlapWeight ρ σ i j * σ.positive.isHermitian.eigenvalues j ^ (-(α - 1) / α) := by
  let P := CFC.rpow σ.matrix (sandwichExponent α)
  have hP : P.IsHermitian := CFC.rpow_nonneg.posSemidef.isHermitian
  have hp : sandwichExponent α + sandwichExponent α = -(α - 1) / α := by
    unfold sandwichExponent
    ring
  have hpn : sandwichExponent α + sandwichExponent α ≠ 0 := by
    have hb := sandwichExponent_neg hα
    linarith
  have hPP : P * P = CFC.rpow σ.matrix (-(α - 1) / α) := by
    rw [← hp]
    exact (rpow_add_of_sum_ne_zero σ.matrix σ.positive _ _ hpn).symm
  have hσ : σ.matrix = (σ.positive.isHermitian.eigenvectorUnitary : Operator n) *
      diagonal (fun i => (σ.positive.isHermitian.eigenvalues i : ℂ)) *
      (σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      using σ.positive.isHermitian.spectral_theorem
  have hc := cfc_of_unitary_diagonalization σ.positive.isHermitian.eigenvectorUnitary
    σ.positive.isHermitian.eigenvalues (fun x : ℝ => x ^ (-(α - 1) / α))
  rw [← hσ, ← matrix_rpow_eq_cfc σ.matrix σ.positive] at hc
  have hmiddle : (ρ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
      (P * P) * (ρ.positive.isHermitian.eigenvectorUnitary : Operator n) =
      (eigenbasisChange ρ σ : Operator n) *
      diagonal (fun j => ((σ.positive.isHermitian.eigenvalues j ^ (-(α - 1) / α) : ℝ) : ℂ)) *
      (eigenbasisChange ρ σ : Operator n)ᴴ := by
    rw [hPP, hc, eigenbasisChange_coe, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  change (((P * spectralFactor ρ)ᴴ * (P * spectralFactor ρ)) i i).re = _
  rw [Matrix.conjTranspose_mul, hP.eq, spectralFactor, Matrix.conjTranspose_mul,
    Matrix.diagonal_conjTranspose]
  simp only [Pi.star_def, Complex.star_def, Complex.conj_ofReal]
  have hmatrix :
      ((diagonal (fun j => (Real.sqrt (ρ.positive.isHermitian.eigenvalues j) : ℂ)) *
        (ρ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ) * P *
          (P * ((ρ.positive.isHermitian.eigenvectorUnitary : Operator n) *
            diagonal (fun j => (Real.sqrt (ρ.positive.isHermitian.eigenvalues j) : ℂ))))) =
      diagonal (fun j => (Real.sqrt (ρ.positive.isHermitian.eigenvalues j) : ℂ)) *
        ((ρ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ * (P * P) *
          (ρ.positive.isHermitian.eigenvectorUnitary : Operator n)) *
        diagonal (fun j => (Real.sqrt (ρ.positive.isHermitian.eigenvalues j) : ℂ)) := by
    simp only [Matrix.mul_assoc]
  rw [hmatrix, hmiddle, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hdiag := unitary_diagonal_entry (eigenbasisChange ρ σ)
    (fun j => σ.positive.isHermitian.eigenvalues j ^ (-(α - 1) / α)) i
  rw [mul_right_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt (ρ.positive.eigenvalues_nonneg i)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hdiag]
  rfl

/-- The noncommutative quasi-divergence dominates the explicit finite scalar expression. -/
theorem scalar_expression_le_quasi (α : ℝ) (hα : 1 < α) (ρ σ : State n) :
    (∑ i, (ρ.positive.isHermitian.eigenvalues i *
      ∑ j, overlapWeight ρ σ i j * σ.positive.isHermitian.eigenvalues j ^ (-(α - 1) / α)) ^ α) ≤
    quasi α ρ.matrix σ.matrix := by
  rw [quasi_eq_spectralFactor_gram]
  have h := sum_diagonal_rpow_le_trace
    ((CFC.rpow σ.matrix (sandwichExponent α) * spectralFactor ρ)ᴴ *
      (CFC.rpow σ.matrix (sandwichExponent α) * spectralFactor ρ))
    (Matrix.posSemidef_conjTranspose_mul_self _) α hα.le
  simpa only [spectralFactor_gram_diagonal α hα ρ σ] using h

end QuantumChannelStein.SandwichedRenyi
