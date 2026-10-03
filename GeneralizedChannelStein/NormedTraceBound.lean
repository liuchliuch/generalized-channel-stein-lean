import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Trace

/-! # Dimension-sharp trace bound in arbitrary finite-dimensional complex norms -/
noncomputable section
namespace GeneralizedChannelStein.NormedTraceBound
open Matrix Polynomial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- No choice of Hilbert norm is required: eigenvalues of a bounded endomorphism
are bounded by its actual operator norm. -/
theorem eigenvalue_norm_le (T : E →L[ℂ] E) (z : ℂ)
    (hz : Module.End.HasEigenvalue T.toLinearMap z) : ‖z‖ ≤ ‖T‖ := by
  obtain ⟨x,hx⟩ := hz.exists_hasEigenvector
  have hn := T.le_opNorm x
  rw [show T x = z • x from hx.apply_eq_smul, norm_smul] at hn
  exact (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hx.2)).mp hn

/-- The exact finite-dimensional trace/operator-norm bound, including dimension zero. -/
theorem norm_trace_le_finrank_mul_norm (T : E →L[ℂ] E) :
    ‖LinearMap.trace ℂ E T.toLinearMap‖ ≤ (Module.finrank ℂ E : ℝ)*‖T‖ := by
  classical
  let b := Module.finBasis ℂ E
  let A := T.toLinearMap.toMatrix b b
  have hroot (z : ℂ) (hz : z ∈ A.charpoly.roots) : ‖z‖ ≤ ‖T‖ := by
    have hs : z ∈ spectrum ℂ A := Matrix.mem_spectrum_of_isRoot_charpoly
      ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mp hz)
    change z ∈ spectrum ℂ (T.toLinearMap.toMatrix b b) at hs
    rw [LinearMap.spectrum_toMatrix] at hs
    exact eigenvalue_norm_le T z (Module.End.HasEigenvalue.of_mem_spectrum hs)
  have hsum : ∀ s : Multiset ℂ, (∀ z ∈ s, ‖z‖ ≤ ‖T‖) → ‖s.sum‖ ≤ (s.card:ℝ)*‖T‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons z s ih =>
      intro h
      have hz := h z (by simp)
      have hs := ih (fun w hw => h w (by simp [hw]))
      simpa only [Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul, add_comm] using (norm_add_le z s.sum).trans (add_le_add hz hs)
  have hc : A.charpoly.roots.card = Module.finrank ℂ E := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
    simp
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_eq_sum_roots_charpoly]
  exact (hsum A.charpoly.roots hroot).trans_eq (by rw [hc])

end GeneralizedChannelStein.NormedTraceBound
