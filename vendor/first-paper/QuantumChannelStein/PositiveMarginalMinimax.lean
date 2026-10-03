import QuantumChannelStein.TestingSDPStrong

/-! # Uniform operator-cost witnesses from actual state expectations
This is the compact minimax step for the geometric-mean channel program.
The marginal is an actual real-linear matrix map and positivity is checked
on its concrete convex feasible set.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.PositiveMarginalMinimax
open Matrix Set TestingSDP
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {a n : ℕ}
local instance positiveMarginalMinimaxCStar1 : CStarAlgebra (Operator a) := CStarAlgebra.mk

def densitySet (a : ℕ) : Set (Operator a) := {X | X.PosSemidef ∧ X.trace = 1}

theorem compact_densitySet (a : ℕ) : IsCompact (densitySet a) := by
  have htrace : Continuous (fun X : Operator a => X.trace) := by unfold Matrix.trace; fun_prop
  have hclosed : IsClosed (densitySet a) := by
    have hp : IsClosed {X : Operator a | (0 : Operator a) ≤ X} := isClosed_le continuous_const continuous_id
    have ht : IsClosed {X : Operator a | X.trace = (1 : ℂ)} := isClosed_eq htrace continuous_const
    simpa only [densitySet, Matrix.nonneg_iff_posSemidef, Set.setOf_and] using hp.inter ht
  apply Metric.isCompact_of_isClosed_isBounded hclosed
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  intro X hX
  exact state_norm_le_one ⟨X, hX.1, hX.2⟩

theorem convex_densitySet (a : ℕ) : Convex ℝ (densitySet a) := by
  intro X hX Y hY r s hr hs hrs
  refine ⟨(hX.1.smul hr).add (hY.1.smul hs), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX.2, hY.2,
    ← add_smul, hrs, one_smul]

def expectation (L : Operator n →ₗ[ℝ] Operator a) (X : Operator n) (omega : Operator a) : ℝ :=
  (L X * omega).trace.re

theorem continuous_expectation (L : Operator n →ₗ[ℝ] Operator a) :
    Continuous (fun z : Operator n × Operator a => expectation L z.1 z.2) := by
  have hL := L.continuous_of_finiteDimensional
  unfold expectation Matrix.trace
  fun_prop

theorem expectation_mix_left (L : Operator n →ₗ[ℝ] Operator a)
    (X Y : Operator n) (omega : Operator a) (r s : ℝ) :
    expectation L (r • X + s • Y) omega =
      r * expectation L X omega + s * expectation L Y omega := by
  simp [expectation, map_add, map_smul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul]

theorem expectation_mix_right (L : Operator n →ₗ[ℝ] Operator a)
    (X : Operator n) (omega tau : Operator a) (r s : ℝ) :
    expectation L X (r • omega + s • tau) =
      r * expectation L X omega + s * expectation L X tau := by
  simp [expectation, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul]

/-- Actual pointwise witnesses give one uniform positive marginal norm bound. -/
theorem exists_uniform_marginal_bound (omega0 : State a)
    (L : Operator n →ₗ[ℝ] Operator a) (T : Set (Operator n)) (hT : Convex ℝ T)
    (hpos : ∀ X ∈ T, (L X).PosSemidef) (r s : ℝ) (hrs : r < s)
    (hpoint : ∀ omega : State a, ∃ X ∈ T, expectation L X omega.matrix < r) :
    ∃ X ∈ T, ‖L X‖ ≤ s := by
  have hconv : ∀ omega ∈ densitySet a, QuasiconvexOn ℝ T (fun X => expectation L X omega) := by
    intro omega homega
    apply ConvexOn.quasiconvexOn
    refine ⟨hT, ?_⟩
    intro X hX Y hY u v hu hv huv
    dsimp only
    rw [expectation_mix_left]
    simp only [smul_eq_mul]
    exact le_rfl
  have hconc : ∀ X ∈ T, QuasiconcaveOn ℝ (densitySet a) (expectation L X) := by
    intro X hX
    apply ConcaveOn.quasiconcaveOn
    refine ⟨convex_densitySet a, ?_⟩
    intro omega ho tau ht u v hu hv huv
    rw [expectation_mix_right]
    simp only [smul_eq_mul]
    exact le_rfl
  obtain ⟨X, hX, hbound⟩ := TestingSDPStrong.exists_uniform_bound_of_pointwise
    (compact_densitySet a) ⟨omega0.matrix, omega0.positive, omega0.trace_one⟩
    (convex_densitySet a) hT (continuous_expectation L) hconv hconc hrs
    (fun omega homega => hpoint ⟨omega, homega.1, homega.2⟩)
  refine ⟨X, hX, norm_le_of_state_expectations omega0 (L X) (hpos X hX) s ?_⟩
  intro omega
  exact (hbound omega.matrix ⟨omega.positive, omega.trace_one⟩).le

end QuantumChannelStein.PositiveMarginalMinimax
