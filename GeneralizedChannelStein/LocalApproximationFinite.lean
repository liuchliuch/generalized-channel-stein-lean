import GeneralizedChannelStein.LocalApproximation
import GeneralizedChannelStein.QuantitativeFamilies

/-! Physical finite-coordinate wrappers for weighted local approximation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TensorPower TensorPermutation ChannelPowerReindex PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {d n : ℕ}

def recursiveOperator (W : Operator (d^n)) : Matrix (Index (Fin d) n) (Index (Fin d) n) ℂ :=
  Matrix.reindex (channelIndexEquiv d n).symm (channelIndexEquiv d n).symm W

theorem recursiveOperator_invariant (W : Operator (d^n))
    (hW : ∀ π : Equiv.Perm (Fin n), Matrix.reindex (sitePermutation d n π)
      (sitePermutation d n π) W=W) : recursiveOperator W∈invariantAlgebra (Fin d) n := by
  intro π
  have h := congrArg (Matrix.reindex (channelIndexEquiv d n).symm
    (channelIndexEquiv d n).symm) (hW π)
  ext i j
  simpa [recursiveOperator,sitePermutation,conjugation,Matrix.reindexAlgEquiv_apply,
    Matrix.reindex_apply,Matrix.submatrix_submatrix] using congrFun (congrFun h i) j

theorem norm_recursiveOperator (W : Operator (d^n)) : ‖recursiveOperator W‖=‖W‖ :=
  TensorPower.norm_reindex _ _ _

/-- Physical block-coordinate weighted discard. -/
def finiteWeightedExpectation (τ : State d) (k m : ℕ) (W : Operator (d^(k+m))) : Operator (d^k) :=
  weightedDiscard (statePower τ m)
    (Matrix.reindex ((channelAddEquiv d k m).symm.trans finProdFinEquiv.symm)
      ((channelAddEquiv d k m).symm.trans finProdFinEquiv.symm) W)

theorem finiteWeightedExpectation_eq (τ : State d) (k m : ℕ) (W : Operator (d^(k+m))) :
    weightedPowerMap τ k m (recursiveOperator W) =
      Matrix.reindex (channelIndexEquiv d k).symm (channelIndexEquiv d k).symm
        (finiteWeightedExpectation τ k m W) := by
  rw [weightedPowerMap_apply]
  congr 2
  ext i j
  simp [recursiveOperator,finiteWeightedExpectation,weightedSplitEquiv,channelAddEquiv,channelConcatEquiv,
    Matrix.reindex_apply,Matrix.submatrix_submatrix]

end GeneralizedChannelStein
