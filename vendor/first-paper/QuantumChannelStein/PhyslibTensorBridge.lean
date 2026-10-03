import QuantumChannelStein.PhyslibStateBridge
import QuantumChannelStein.TensorPower
import StateSteinDirect

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.PhyslibStateBridge
open Matrix TensorPower Filter
open scoped BigOperators ComplexOrder Topology

/-- Literal coordinate equivalence, retaining the one-dimensional zeroth power. -/
def tupleEquiv (d : Type*) : (m : ℕ) → Index d m ≃ (Fin m → d)
  | 0 => Equiv.ofUnique _ _
  | m + 1 => ((Equiv.refl d).prodCongr (tupleEquiv d m)).trans (Fin.consEquiv (fun _ : Fin (m + 1) => d))

/-- Both tensor conventions multiply exactly the same matrix entries. -/
theorem tensorPower_entries {d : Type*} (A : Matrix d d ℂ) (m : ℕ)
    (x y : Index d m) :
    tensorPower A m x y = ∏ i : Fin m,
      A (tupleEquiv d m x i) (tupleEquiv d m y i) := by
  induction m with
  | zero => simp [tensorPower]
  | succ m ih =>
    rw [tensorPower_succ, Matrix.kroneckerMap_apply, Fin.prod_univ_succ]
    change A x.1 y.1 * tensorPower A m x.2 y.2 =
      A x.1 y.1 * ∏ i : Fin m,
        A (tupleEquiv d m x.2 i) (tupleEquiv d m y.2 i)
    rw [ih]

/-- The concrete source state power becomes the local recursive tensor power. -/
theorem npow_reindex {d : ℕ} (rho : State d) (m : ℕ) :
    Matrix.reindex (tupleEquiv (Fin d) m).symm (tupleEquiv (Fin d) m).symm
      ((toMState rho).npow m).m = tensorPower rho.matrix m := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [StateSteinAudit.npow_entries, tensorPower_entries]
  rfl

private theorem trace_reindex {d e : Type*} [Fintype d] [Fintype e]
    (e : d ≃ e) (A : Matrix d d ℂ) : (Matrix.reindex e e A).trace = A.trace := by
  exact e.symm.sum_comp (fun i => A i i)

/-- Changing tensor coordinates preserves the literal Born expectation. -/
theorem npow_exp_val_eq {d : ℕ} (rho : State d) (m : ℕ)
    (T : HermitianMat (Fin m → Fin d) ℂ) :
    ((toMState rho).npow m).exp_val T =
      (tensorPower rho.matrix m *
        Matrix.reindex (tupleEquiv (Fin d) m).symm (tupleEquiv (Fin d) m).symm T.mat).trace.re := by
  rw [← npow_reindex rho m]
  let e := (tupleEquiv (Fin d) m).symm
  change _ = ((Matrix.reindexLinearEquiv ℂ ℂ e e ((toMState rho).npow m).m) *
    (Matrix.reindexLinearEquiv ℂ ℂ e e T.mat)).trace.re
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_apply, trace_reindex]
  exact HermitianMat.inner_eq_re_trace _ _

end QuantumChannelStein.PhyslibStateBridge
