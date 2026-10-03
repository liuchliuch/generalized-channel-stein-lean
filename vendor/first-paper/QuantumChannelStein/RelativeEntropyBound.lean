import QuantumChannelStein.RelativeEntropyNonneg
import QuantumChannelStein.RelativeEntropyScalarBound
import QuantumChannelStein.Factorization

/-!
# Relative entropy under scalar positive-semidefinite domination

The proof factors explicit spectral square roots using Douglas's theorem,
then bounds an inverse-eigenvalue sum by the factor's operator norm. A
scalar logarithm inequality supplies the entropy upper bound; no operator
logarithm monotonicity or data-processing axiom is assumed.
-/

noncomputable section
namespace QuantumChannelStein.RelativeEntropy

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

/-- An explicit spectral Gram factor, not necessarily a Hermitian square
root: its columns are square-root-weighted eigenvectors. -/
def spectralFactor (ρ : State n) : Operator n :=
  (ρ.positive.isHermitian.eigenvectorUnitary : Operator n) *
    Matrix.diagonal (fun i => (Real.sqrt (ρ.positive.isHermitian.eigenvalues i) : ℂ))

theorem spectralFactor_mul_conjTranspose (ρ : State n) :
    spectralFactor ρ * (spectralFactor ρ)ᴴ = ρ.matrix := by
  rw [spectralFactor, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
  simp only [Pi.star_def, Complex.star_def, Complex.conj_ofReal]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
    Matrix.diagonal_mul_diagonal]
  have hdiag : (fun i =>
      (Real.sqrt (ρ.positive.isHermitian.eigenvalues i) : ℂ) *
        (Real.sqrt (ρ.positive.isHermitian.eigenvalues i) : ℂ)) =
      (fun i => (ρ.positive.isHermitian.eigenvalues i : ℂ)) := by
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (ρ.positive.eigenvalues_nonneg i)]
  rw [hdiag, ← Matrix.mul_assoc]
  simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    using ρ.positive.isHermitian.spectral_theorem.symm

/-- PSD domination produces a factor of the spectral Gram matrices with
the sharp square-root operator-norm bound. -/
theorem exists_spectralFactor_domination (ρ σ : State n) (c : ℝ) (hc : 0 ≤ c)
    (h : (c • σ.matrix - ρ.matrix).PosSemidef) :
    ∃ D : Operator n, spectralFactor ρ = spectralFactor σ * D ∧ ‖D‖ ≤ Real.sqrt c := by
  apply Factorization.matrix_factorization (spectralFactor ρ) (spectralFactor σ) hc
  simpa only [spectralFactor_mul_conjTranspose] using h

/-- An entry of a Douglas factor relates the two eigenvalues and their
squared eigenbasis overlap. -/
theorem spectralFactor_entry_normSq (ρ σ : State n) (D : Operator n)
    (hD : spectralFactor ρ = spectralFactor σ * D) (i j : Fin n) :
    ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j =
      σ.positive.isHermitian.eigenvalues j * Complex.normSq (D j i) := by
  have h := congrArg
    (fun A : Operator n => ((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ * A) j i)
    hD
  have hstar : (σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
      (σ.positive.isHermitian.eigenvectorUnitary : Operator n) = 1 :=
    unitary.coe_star_mul_self _
  have hchange : (σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
      (ρ.positive.isHermitian.eigenvectorUnitary : Operator n) =
      (eigenbasisChange ρ σ : Operator n)ᴴ := by
    rw [eigenbasisChange_coe, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  simp only [spectralFactor, ← Matrix.mul_assoc, hstar, Matrix.one_mul, hchange,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at h
  have hn := congrArg Complex.normSq h
  simp only [map_mul, Complex.star_def, Complex.normSq_conj, Complex.normSq_ofReal,
    Real.mul_self_sqrt (ρ.positive.eigenvalues_nonneg i),
    Real.mul_self_sqrt (σ.positive.eigenvalues_nonneg j)] at hn
  unfold overlapWeight
  nlinarith [hn]

/-- Each matrix column has squared Euclidean norm at most the square of
the Hilbert operator norm. -/
theorem sum_column_normSq_le (D : Operator n) (i : Fin n) :
    ∑ j, Complex.normSq (D j i) ≤ ‖D‖ ^ 2 := by
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  have h := Matrix.l2_opNorm_mulVec D e
  change ‖WithLp.toLp 2 (D *ᵥ WithLp.ofLp e)‖ ≤ ‖D‖ * ‖e‖ at h
  rw [he, mul_one] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa [EuclideanSpace.norm_sq_eq, e, EuclideanSpace.ofLp_single,
    Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply,
    ← Complex.normSq_eq_norm_sq] using hsq

/-- The reciprocal-eigenvalue overlap sum is bounded directly by the
finite domination constant. Zero denominators use totalized division and
are controlled by support inclusion in the subsequent entropy estimate. -/
theorem reciprocal_overlap_sum_le (ρ σ : State n) (c : ℝ) (hc : 0 ≤ c)
    (h : (c • σ.matrix - ρ.matrix).PosSemidef) (i : Fin n) :
    (∑ j, ρ.positive.isHermitian.eigenvalues i * overlapWeight ρ σ i j /
      σ.positive.isHermitian.eigenvalues j) ≤ c := by
  obtain ⟨D, hD, hn⟩ := exists_spectralFactor_domination ρ σ c hc h
  calc
    _ ≤ ∑ j, Complex.normSq (D j i) := by
      apply Finset.sum_le_sum
      intro j _
      rw [spectralFactor_entry_normSq ρ σ D hD i j]
      by_cases hj : σ.positive.isHermitian.eigenvalues j = 0
      · simp only [hj, zero_mul, zero_div]
        exact Complex.normSq_nonneg _
      · rw [mul_div_cancel_left₀ _ hj]
    _ ≤ ‖D‖ ^ 2 := sum_column_normSq_le D i
    _ ≤ (Real.sqrt c) ^ 2 := pow_le_pow_left₀ (norm_nonneg D) hn 2
    _ = c := Real.sq_sqrt hc

/-- Finite scalar domination gives the logarithmic upper bound on the
actual trace formula, without any invertibility assumptions. -/
theorem traceFormula_le_log2_of_domination (ρ σ : State n) (c : ℝ) (hc : 1 ≤ c)
    (h : (c • σ.matrix - ρ.matrix).PosSemidef) :
    traceFormula ρ σ ≤ Real.logb 2 c := by
  have hs : supportIncluded ρ σ :=
    SupportDomination.ker_le_of_posSemidef_smul_sub ρ.positive h
  rw [traceFormula_eq_overlap_sum]
  exact row_stochastic_entropy_upper_log2
    ρ.positive.isHermitian.eigenvalues σ.positive.isHermitian.eigenvalues
    (overlapWeight ρ σ) c ρ.positive.eigenvalues_nonneg σ.positive.eigenvalues_nonneg
    (sum_eigenvalues_eq_one ρ) (overlapWeight_nonneg ρ σ)
    (sum_overlapWeight_row ρ σ) hc (eigenvalue_mul_overlap_eq_zero ρ σ hs)
    (reciprocal_overlap_sum_le ρ σ c (le_trans zero_le_one hc) h)

/-- Umegaki relative entropy is at most the logarithm of any finite
positive-semidefinite domination constant at least one. -/
theorem umegaki_le_log2_of_domination (ρ σ : State n) (c : ℝ) (hc : 1 ≤ c)
    (h : (c • σ.matrix - ρ.matrix).PosSemidef) :
    umegaki ρ σ ≤ (Real.logb 2 c : EReal) := by
  have hs : supportIncluded ρ σ :=
    SupportDomination.ker_le_of_posSemidef_smul_sub ρ.positive h
  rw [umegaki_of_supportIncluded ρ σ hs, EReal.coe_le_coe_iff]
  exact traceFormula_le_log2_of_domination ρ σ c hc h

end QuantumChannelStein.RelativeEntropy
