import QuantumChannelStein.RelativeEntropyTensor
import QuantumChannelStein.ChannelEntropyRates

/-! # Entropy invariance under actual finite coordinate permutations -/

noncomputable section
namespace QuantumChannelStein

open Matrix SpectralDecomposition
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace State
variable {n m : ℕ}

/-- Simultaneously relabel a density matrix's row and column coordinates. -/
def reindex (e : Fin n ≃ Fin m) (ρ : State n) : State m where
  matrix := Matrix.reindex e e ρ.matrix
  positive := ρ.positive.submatrix e.symm
  trace_one := (ChannelEntropy.trace_reindex_equiv e ρ.matrix).trans ρ.trace_one

@[simp] theorem reindex_matrix (e : Fin n ≃ Fin m) (ρ : State n) :
    (reindex e ρ).matrix = Matrix.reindex e e ρ.matrix := rfl

end State

namespace RelativeEntropy
variable {n m : ℕ}

theorem supportIncluded_reindex (e : Fin n ≃ Fin m) (ρ σ : State n) :
    supportIncluded (ρ.reindex e) (σ.reindex e) ↔ supportIncluded ρ σ :=
  reindex_kernel_inclusion_iff e ρ.matrix σ.matrix ρ.positive σ.positive

theorem traceFormula_reindex (e : Fin n ≃ Fin m) (ρ σ : State n) :
    traceFormula (ρ.reindex e) (σ.reindex e) = traceFormula ρ σ := by
  simp only [traceFormula, State.reindex_matrix, spectralLog2_eq_cfc]
  rw [cfc_reindex e ρ.matrix ρ.positive.isHermitian,
    cfc_reindex e σ.matrix σ.positive.isHermitian]
  change (((reindexHom e) ρ.matrix) * ((reindexHom e) (cfc (Real.logb 2) ρ.matrix) -
    (reindexHom e) (cfc (Real.logb 2) σ.matrix))).trace.re = _
  rw [← map_sub, ← map_mul]
  exact congrArg Complex.re (ChannelEntropy.trace_reindex_equiv e _)

/-- The full support-aware EReal divergence is invariant under coordinate
permutations, including its infinite branch. -/
theorem umegaki_reindex (e : Fin n ≃ Fin m) (ρ σ : State n) :
    umegaki (ρ.reindex e) (σ.reindex e) = umegaki ρ σ := by
  unfold umegaki
  rw [supportIncluded_reindex e ρ σ, traceFormula_reindex e ρ σ]

end RelativeEntropy
end QuantumChannelStein
