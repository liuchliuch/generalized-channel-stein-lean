import QuantumChannelStein.StateTensor
import QuantumChannelStein.SpectralDecompositionCFC
import Mathlib.Data.EReal.Operations

/-! # Additivity of the actual finite-state Umegaki relative entropy -/

noncomputable section
namespace QuantumChannelStein.RelativeEntropy

open Matrix SpectralDecomposition
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

variable {n m : ℕ}

/-- Tensor product of two actual unitary eigenbasis matrices. -/
def tensorUnitary {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ := by
  refine ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ), ?_⟩
  have hUl : (U : Matrix ι ι ℂ)ᴴ * U = 1 := unitary.star_mul_self_of_mem U.property
  have hUr : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 := unitary.mul_star_self_of_mem U.property
  have hVl : (V : Matrix κ κ ℂ)ᴴ * V = 1 := unitary.star_mul_self_of_mem V.property
  have hVr : (V : Matrix κ κ ℂ) * (V : Matrix κ κ ℂ)ᴴ = 1 := unitary.mul_star_self_of_mem V.property
  rw [unitary.mem_iff]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, hUl, hUr, hVl, hVr, Matrix.one_kronecker_one, and_self]

/-- The product eigenbasis is a proved diagonalization of a state product. -/
theorem kronecker_spectral (σ : State n) (υ : State m) :
    σ.matrix ⊗ₖ υ.matrix =
      (tensorUnitary σ.positive.isHermitian.eigenvectorUnitary
        υ.positive.isHermitian.eigenvectorUnitary : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) *
      Matrix.diagonal (fun p =>
        ((σ.positive.isHermitian.eigenvalues p.1 * υ.positive.isHermitian.eigenvalues p.2 : ℝ) : ℂ)) *
      (tensorUnitary σ.positive.isHermitian.eigenvectorUnitary
        υ.positive.isHermitian.eigenvectorUnitary : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ)ᴴ := by
  have hs := σ.positive.isHermitian.spectral_theorem
  have ht := υ.positive.isHermitian.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at hs ht
  conv_lhs => arg 2; rw [hs]
  conv_lhs => arg 3; rw [ht]
  simp only [tensorUnitary, Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
    Matrix.diagonal_kronecker_diagonal, Function.comp_apply, Complex.ofReal_mul,
    Matrix.star_eq_conjTranspose]
  rfl

/-- Complex weight of the first state in the second state's eigenbasis. -/
def spectralWeight (ρ σ : State n) (i : Fin n) : ℂ :=
  ((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
    ρ.matrix * (σ.positive.isHermitian.eigenvectorUnitary : Operator n)) i i

theorem sum_spectralWeight (ρ σ : State n) : ∑ i, spectralWeight ρ σ i = 1 := by
  change ((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
    ρ.matrix * (σ.positive.isHermitian.eigenvectorUnitary : Operator n)).trace = 1
  rw [trace_unitary_conjugate, ρ.trace_one]

theorem spectralWeight_zero (ρ σ : State n) (h : supportIncluded ρ σ)
    (i : Fin n) (hi : σ.positive.isHermitian.eigenvalues i = 0) : spectralWeight ρ σ i = 0 := by
  have hvec : ((σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ *
    ρ.matrix * (σ.positive.isHermitian.eigenvectorUnitary : Operator n)) *ᵥ Pi.single i 1 = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      σ.positive.isHermitian.eigenvectorUnitary_mulVec,
      mulVec_eigenvector_eq_zero_of_supportIncluded ρ σ h i hi, Matrix.mulVec_zero]
  simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply, Pi.zero_apply]
    using congrFun hvec i

/-- Full complex version of the finite CFC trace formula. -/
theorem trace_mul_cfc_eq_spectral_complex (ρ σ : State n) (f : ℝ → ℝ) :
    (ρ.matrix * cfc f σ.matrix).trace =
      ∑ i, spectralWeight ρ σ i * (f (σ.positive.isHermitian.eigenvalues i) : ℂ) := by
  have h := trace_mul_cfc_diagonalization ρ.matrix σ.positive.isHermitian.eigenvectorUnitary
    σ.positive.isHermitian.eigenvalues f
  have hs : σ.matrix =
      (σ.positive.isHermitian.eigenvectorUnitary : Operator n) *
        Matrix.diagonal (fun i => (σ.positive.isHermitian.eigenvalues i : ℂ)) *
        (σ.positive.isHermitian.eigenvectorUnitary : Operator n)ᴴ :=
    by simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
      using σ.positive.isHermitian.spectral_theorem
  rw [← hs] at h
  exact h

/-- Full complex trace on a product state in the proved product eigenbasis. -/
theorem trace_mul_cfc_kronecker (ρ σ : State n) (τ υ : State m) (f : ℝ → ℝ) :
    ((ρ.matrix ⊗ₖ τ.matrix) * cfc f (σ.matrix ⊗ₖ υ.matrix)).trace =
      ∑ i, ∑ j, spectralWeight ρ σ i * spectralWeight τ υ j *
        (f (σ.positive.isHermitian.eigenvalues i * υ.positive.isHermitian.eigenvalues j) : ℂ) := by
  rw [kronecker_spectral σ υ, trace_mul_cfc_diagonalization]
  simp only [tensorUnitary, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, spectralWeight]

/-- Canonical index flattening leaves a CFC cross trace unchanged. -/
theorem trace_mul_cfc_tensor (ρ σ : State n) (τ υ : State m) (f : ℝ → ℝ) :
    ((ρ.tensor τ).matrix * cfc f (σ.tensor υ).matrix).trace =
      ((ρ.matrix ⊗ₖ τ.matrix) * cfc f (σ.matrix ⊗ₖ υ.matrix)).trace := by
  rw [State.tensor_matrix, State.tensor_matrix,
    cfc_reindex finProdFinEquiv _ (MatrixMap.posSemidef_kronecker σ.positive υ.positive).isHermitian]
  change (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv _ *
    Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv _).trace = _
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_apply,
    ChannelEntropy.trace_reindex_equiv]

/-- The logarithmic cross trace splits on supported state products. The
zero eigenvalues are eliminated by proved zero spectral weights, before
using the scalar logarithm product identity. -/
theorem trace_mul_spectralLog2_tensor (ρ σ : State n) (τ υ : State m)
    (hρ : supportIncluded ρ σ) (hτ : supportIncluded τ υ) :
    ((ρ.tensor τ).matrix * spectralLog2 (σ.tensor υ)).trace =
      (ρ.matrix * spectralLog2 σ).trace + (τ.matrix * spectralLog2 υ).trace := by
  simp only [spectralLog2_eq_cfc]
  rw [trace_mul_cfc_tensor, trace_mul_cfc_kronecker,
    trace_mul_cfc_eq_spectral_complex, trace_mul_cfc_eq_spectral_complex]
  have hterm (i : Fin n) (j : Fin m) :
      spectralWeight ρ σ i * spectralWeight τ υ j *
        (Real.logb 2 (σ.positive.isHermitian.eigenvalues i * υ.positive.isHermitian.eigenvalues j) : ℂ) =
      (spectralWeight ρ σ i * (Real.logb 2 (σ.positive.isHermitian.eigenvalues i) : ℂ)) *
        spectralWeight τ υ j + spectralWeight ρ σ i *
          (spectralWeight τ υ j * (Real.logb 2 (υ.positive.isHermitian.eigenvalues j) : ℂ)) := by
    by_cases hi : σ.positive.isHermitian.eigenvalues i = 0
    · rw [spectralWeight_zero ρ σ hρ i hi]
      simp
    by_cases hj : υ.positive.isHermitian.eigenvalues j = 0
    · rw [spectralWeight_zero τ υ hτ j hj]
      simp
    rw [Real.logb_mul hi hj, Complex.ofReal_add]
    ring
  calc
    _ = (∑ i, spectralWeight ρ σ i * (Real.logb 2 (σ.positive.isHermitian.eigenvalues i) : ℂ)) *
        (∑ j, spectralWeight τ υ j) +
      (∑ i, spectralWeight ρ σ i) *
        (∑ j, spectralWeight τ υ j * (Real.logb 2 (υ.positive.isHermitian.eigenvalues j) : ℂ)) := by
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i j
    _ = _ := by rw [sum_spectralWeight, sum_spectralWeight, mul_one, one_mul]

/-- Additivity of the finite trace formula on supported tensor products. -/
theorem traceFormula_tensor (ρ σ : State n) (τ υ : State m)
    (hρ : supportIncluded ρ σ) (hτ : supportIncluded τ υ) :
    traceFormula (ρ.tensor τ) (σ.tensor υ) = traceFormula ρ σ + traceFormula τ υ := by
  simp only [traceFormula, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [trace_mul_spectralLog2_tensor ρ ρ τ τ (supportIncluded_refl ρ) (supportIncluded_refl τ),
    trace_mul_spectralLog2_tensor ρ σ τ υ hρ hτ]
  simp only [Complex.add_re]
  ring

/-- Genuine Umegaki tensor additivity, with the correct extended-real
infinite branches and no invertibility assumptions on any state. -/
theorem umegaki_tensor (ρ σ : State n) (τ υ : State m) :
    umegaki (ρ.tensor τ) (σ.tensor υ) = umegaki ρ σ + umegaki τ υ := by
  classical
  by_cases hρ : supportIncluded ρ σ
  · by_cases hτ : supportIncluded τ υ
    · rw [umegaki_of_supportIncluded _ _ ((supportIncluded_tensor_iff ρ σ τ υ).mpr ⟨hρ, hτ⟩),
        umegaki_of_supportIncluded ρ σ hρ, umegaki_of_supportIncluded τ υ hτ,
        traceFormula_tensor ρ σ τ υ hρ hτ, EReal.coe_add]
    · have ht : ¬ supportIncluded (ρ.tensor τ) (σ.tensor υ) :=
        fun ht => hτ ((supportIncluded_tensor_iff ρ σ τ υ).mp ht).2
      rw [umegaki_of_not_supportIncluded _ _ ht, umegaki_of_not_supportIncluded τ υ hτ,
        EReal.add_top_of_ne_bot (umegaki_ne_bot ρ σ)]
  · have ht : ¬ supportIncluded (ρ.tensor τ) (σ.tensor υ) :=
      fun ht => hρ ((supportIncluded_tensor_iff ρ σ τ υ).mp ht).1
    rw [umegaki_of_not_supportIncluded _ _ ht, umegaki_of_not_supportIncluded ρ σ hρ,
      EReal.top_add_of_ne_bot (umegaki_ne_bot τ υ)]

end QuantumChannelStein.RelativeEntropy
