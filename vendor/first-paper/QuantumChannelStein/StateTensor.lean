import QuantumChannelStein.ChannelEntropy
import QuantumChannelStein.TensorSupport

/-! # Actual tensor products of finite density matrices and their supports -/

noncomputable section
namespace QuantumChannelStein

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

namespace State

variable {n m : ℕ}

theorem matrix_ne_zero (ρ : State n) : ρ.matrix ≠ 0 := by
  intro h
  have ht := ρ.trace_one
  rw [h, Matrix.trace_zero] at ht
  exact zero_ne_one ht

/-- Independent state product with canonical finite-index flattening. -/
def tensor (ρ : State n) (τ : State m) : State (n * m) where
  matrix := Matrix.reindex finProdFinEquiv finProdFinEquiv (ρ.matrix ⊗ₖ τ.matrix)
  positive := (MatrixMap.posSemidef_kronecker ρ.positive τ.positive).submatrix finProdFinEquiv.symm
  trace_one := by
    rw [ChannelEntropy.trace_reindex_equiv, Matrix.trace_kronecker,
      ρ.trace_one, τ.trace_one, one_mul]

@[simp] theorem tensor_matrix (ρ : State n) (τ : State m) :
    (tensor ρ τ).matrix =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (ρ.matrix ⊗ₖ τ.matrix) := rfl

end State

namespace RelativeEntropy

variable {n m : ℕ}

/-- Support inclusion of nonzero density tensor products is equivalent to
support inclusion in both factors, including all singular cases. -/
theorem supportIncluded_tensor_iff (ρ σ : State n) (τ υ : State m) :
    supportIncluded (ρ.tensor τ) (σ.tensor υ) ↔
      supportIncluded ρ σ ∧ supportIncluded τ υ := by
  change LinearMap.ker (Matrix.reindex finProdFinEquiv finProdFinEquiv
    (σ.matrix ⊗ₖ υ.matrix)).mulVecLin ≤
      LinearMap.ker (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (ρ.matrix ⊗ₖ τ.matrix)).mulVecLin ↔ _
  rw [reindex_kernel_inclusion_iff finProdFinEquiv _ _
    (MatrixMap.posSemidef_kronecker ρ.positive τ.positive)
    (MatrixMap.posSemidef_kronecker σ.positive υ.positive)]
  constructor
  · intro h
    refine ⟨kernel_inclusion_of_tensor ρ.matrix σ.matrix τ.matrix υ.matrix τ.matrix_ne_zero h, ?_⟩
    have hs := (reindex_kernel_inclusion_iff (Equiv.prodComm (Fin n) (Fin m)) _ _
      (MatrixMap.posSemidef_kronecker ρ.positive τ.positive)
      (MatrixMap.posSemidef_kronecker σ.positive υ.positive)).mpr h
    have swap (A : Operator n) (B : Operator m) :
        Matrix.reindex (Equiv.prodComm (Fin n) (Fin m)) (Equiv.prodComm (Fin n) (Fin m))
          (A ⊗ₖ B) = B ⊗ₖ A := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp [Matrix.reindex_apply, mul_comm]
    rw [swap, swap] at hs
    exact kernel_inclusion_of_tensor τ.matrix υ.matrix ρ.matrix σ.matrix ρ.matrix_ne_zero hs
  · rintro ⟨hρ, hτ⟩
    obtain ⟨c, hc, hcp⟩ := (supportIncluded_iff_exists_domination ρ σ).mp hρ
    obtain ⟨d, hd, hdp⟩ := (supportIncluded_iff_exists_domination τ υ).mp hτ
    have ht := (MatrixMap.posSemidef_kronecker hcp (υ.positive.smul (le_trans zero_le_one hd))).add
      (MatrixMap.posSemidef_kronecker ρ.positive hdp)
    have hdom : ((c * d) • (σ.matrix ⊗ₖ υ.matrix) - (ρ.matrix ⊗ₖ τ.matrix)).PosSemidef := by
      convert ht using 1
      ext ⟨i, j⟩ ⟨k, l⟩
      simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
        Complex.real_smul, Complex.ofReal_mul]
      ring
    exact SupportDomination.ker_le_of_posSemidef_smul_sub
      (MatrixMap.posSemidef_kronecker ρ.positive τ.positive) hdom

end RelativeEntropy
end QuantumChannelStein
