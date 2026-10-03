import QuantumChannelStein.SandwichedRenyiBasics
import QuantumChannelStein.RelativeEntropyReindex

/-! # Genuine tensor additivity of support-aware sandwiched Rényi divergence

All powers are evaluated in the actual product eigenbasis. Scalar power
multiplicativity includes zero eigenvalues and negative powers, so the
sandwich identity does not impose faithfulness on either state.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix RelativeEntropy SpectralDecomposition
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] matrixCStar
variable {n m : ℕ}

theorem rpow_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (p : ℝ) :
    CFC.rpow (Matrix.reindex e e A) p = Matrix.reindex e e (CFC.rpow A p) := by
  have hr : (Matrix.reindex e e A).PosSemidef := hA.submatrix e.symm
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hr.nonneg,
    CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA.nonneg]
  exact cfc_reindex e A hA.isHermitian _

theorem rpow_kronecker {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (p : ℝ) :
    CFC.rpow (A ⊗ₖ B) p = CFC.rpow A p ⊗ₖ CFC.rpow B p := by
  let U := hA.isHermitian.eigenvectorUnitary
  let V := hB.isHermitian.eigenvectorUnitary
  let a := hA.isHermitian.eigenvalues
  let b := hB.isHermitian.eigenvalues
  have hAs : A = (U : Matrix ι ι ℂ) * diagonal (fun i => (a i : ℂ)) * (U : Matrix ι ι ℂ)ᴴ := by
    simpa only [U, a, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      using hA.isHermitian.spectral_theorem
  have hBs : B = (V : Matrix κ κ ℂ) * diagonal (fun i => (b i : ℂ)) * (V : Matrix κ κ ℂ)ᴴ := by
    simpa only [V, b, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      using hB.isHermitian.spectral_theorem
  have hABs : A ⊗ₖ B = (tensorUnitary U V : Matrix (ι × κ) (ι × κ) ℂ) *
      diagonal (fun ij => ((a ij.1 * b ij.2 : ℝ) : ℂ)) *
      (tensorUnitary U V : Matrix (ι × κ) (ι × κ) ℂ)ᴴ := by
    rw [hAs, hBs]
    simp only [tensorUnitary, Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal, Complex.ofReal_mul]
  have hfA := cfc_of_unitary_diagonalization U a (fun x : ℝ => x ^ p)
  have hfB := cfc_of_unitary_diagonalization V b (fun x : ℝ => x ^ p)
  have hfAB := cfc_of_unitary_diagonalization (tensorUnitary U V)
    (fun ij => a ij.1 * b ij.2) (fun x : ℝ => x ^ p)
  rw [← hAs] at hfA
  rw [← hBs] at hfB
  rw [← hABs] at hfAB
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real (MatrixMap.posSemidef_kronecker hA hB).nonneg,
    CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA.nonneg,
    CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hB.nonneg, hfA, hfB, hfAB]
  simp only [tensorUnitary, Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
    Matrix.diagonal_kronecker_diagonal]
  congr 2
  congr 1
  funext ij
  simp only [a, b, Real.mul_rpow (hA.eigenvalues_nonneg ij.1) (hB.eigenvalues_nonneg ij.2),
    Complex.ofReal_mul]

theorem sandwichedOperator_reindex (e : Fin n ≃ Fin m) (α : ℝ)
    (A B : Operator n) (hB : B.PosSemidef) :
    sandwichedOperator α (Matrix.reindex e e A) (Matrix.reindex e e B) =
      Matrix.reindex e e (sandwichedOperator α A B) := by
  simp only [sandwichedOperator, rpow_reindex e B hB]
  change reindexHom e _ * reindexHom e _ * reindexHom e _ = reindexHom e (_ * _ * _)
  simp only [map_mul]

theorem quasi_reindex (e : Fin n ≃ Fin m) (α : ℝ) (A B : Operator n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    quasi α (Matrix.reindex e e A) (Matrix.reindex e e B) = quasi α A B := by
  rw [quasi, sandwichedOperator_reindex e α A B hB,
    rpow_reindex e _ (sandwichedOperator_positive α hA), ChannelEntropy.trace_reindex_equiv]
  rfl

theorem renyi_reindex (e : Fin n ≃ Fin m) (α : ℝ) (hα : 1 < α) (ρ σ : State n) :
    renyi α hα (ρ.reindex e) (σ.reindex e) = renyi α hα ρ σ := by
  unfold renyi
  rw [supportIncluded_reindex, State.reindex_matrix, State.reindex_matrix,
    quasi_reindex e α ρ.matrix σ.matrix ρ.positive σ.positive]

theorem sandwichedOperator_tensor (α : ℝ) (ρ σ : State n) (τ υ : State m) :
    sandwichedOperator α (ρ.tensor τ).matrix (σ.tensor υ).matrix =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (sandwichedOperator α ρ.matrix σ.matrix ⊗ₖ sandwichedOperator α τ.matrix υ.matrix) := by
  simp only [sandwichedOperator, State.tensor_matrix,
    rpow_reindex finProdFinEquiv _ (MatrixMap.posSemidef_kronecker σ.positive υ.positive),
    rpow_kronecker σ.matrix υ.matrix σ.positive υ.positive]
  change reindexHom finProdFinEquiv _ * reindexHom finProdFinEquiv _ *
    reindexHom finProdFinEquiv _ = reindexHom finProdFinEquiv _
  simp only [← map_mul, ← Matrix.mul_kronecker_mul]

theorem quasi_tensor (α : ℝ) (ρ σ : State n) (τ υ : State m) :
    quasi α (ρ.tensor τ).matrix (σ.tensor υ).matrix =
      quasi α ρ.matrix σ.matrix * quasi α τ.matrix υ.matrix := by
  have hX := sandwichedOperator_positive α ρ.positive (B := σ.matrix)
  have hY := sandwichedOperator_positive α τ.positive (B := υ.matrix)
  rw [quasi, sandwichedOperator_tensor,
    rpow_reindex finProdFinEquiv _ (MatrixMap.posSemidef_kronecker hX hY),
    rpow_kronecker _ _ hX hY, ChannelEntropy.trace_reindex_equiv, Matrix.trace_kronecker]
  have hi : (CFC.rpow (sandwichedOperator α ρ.matrix σ.matrix) α).trace.im = 0 :=
    (Complex.nonneg_iff.mp CFC.rpow_nonneg.posSemidef.trace_nonneg).2.symm
  simp only [Complex.mul_re, hi, zero_mul, sub_zero, quasi]

/-- Full EReal tensor additivity, including unsupported singular states. -/
theorem renyi_tensor (α : ℝ) (hα : 1 < α) (ρ σ : State n) (τ υ : State m) :
    renyi α hα (ρ.tensor τ) (σ.tensor υ) = renyi α hα ρ σ + renyi α hα τ υ := by
  classical
  by_cases hρ : supportIncluded ρ σ
  · by_cases hτ : supportIncluded τ υ
    · rw [renyi_of_supportIncluded _ _ _ _ ((supportIncluded_tensor_iff ρ σ τ υ).mpr ⟨hρ, hτ⟩),
        renyi_of_supportIncluded α hα ρ σ hρ, renyi_of_supportIncluded α hα τ υ hτ,
        quasi_tensor, Real.logb_mul (state_quasi_pos α hα ρ σ hρ).ne'
          (state_quasi_pos α hα τ υ hτ).ne', add_div, EReal.coe_add]
    · have ht : ¬ supportIncluded (ρ.tensor τ) (σ.tensor υ) :=
        fun ht => hτ ((supportIncluded_tensor_iff ρ σ τ υ).mp ht).2
      rw [renyi_of_not_supportIncluded _ _ _ _ ht, renyi_of_not_supportIncluded α hα τ υ hτ,
        EReal.add_top_of_ne_bot (renyi_ne_bot α hα ρ σ)]
  · have ht : ¬ supportIncluded (ρ.tensor τ) (σ.tensor υ) :=
      fun ht => hρ ((supportIncluded_tensor_iff ρ σ τ υ).mp ht).1
    rw [renyi_of_not_supportIncluded _ _ _ _ ht, renyi_of_not_supportIncluded α hα ρ σ hρ,
      EReal.top_add_of_ne_bot (renyi_ne_bot α hα τ υ)]

end QuantumChannelStein.SandwichedRenyi
