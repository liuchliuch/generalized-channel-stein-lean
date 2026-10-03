import QuantumChannelStein.FaithfulDensity

/-! # Faithful-only pointwise bounds suffice for the compact minimax witness
A concrete identity mixture supplies faithful inputs while controlling every
positive marginal expectation. No continuity of the optimized divergence is
assumed at singular density matrices.
-/
noncomputable section
namespace QuantumChannelStein.PositiveMarginalMinimax
open Matrix FaithfulDensity
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {a n : ℕ}

theorem pointwise_bound_of_faithful (ha : 0 < a)
    (L : Operator n →ₗ[ℝ] Operator a) (T : Set (Operator n))
    (hpos : ∀ X ∈ T, (L X).PosSemidef) (r s : ℝ) (hr : 0 ≤ r) (hrs : r < s)
    (hpoint : ∀ omega : State a, omega.matrix.PosDef → ∃ X ∈ T, expectation L X omega.matrix < r) :
    ∀ omega : State a, ∃ X ∈ T, expectation L X omega.matrix < s := by
  intro omega
  have hs : 0 < s := hr.trans_lt hrs
  let t := (s - r) / (2 * s)
  have ht : 0 < t := div_pos (sub_pos.mpr hrs) (by positivity)
  have ht1 : t < 1 := by
    apply (div_lt_one (by positivity : 0 < 2 * s)).mpr
    linarith
  have hgap : r < (1 - t) * s := by
    have heq : (1 - t) * s = (s + r) / 2 := by dsimp [t]; field_simp; ring
    rw [heq]
    linarith
  let tau := mix omega (maximallyMixed a ha) t ht.le ht1.le
  obtain ⟨X, hX, hv⟩ := hpoint tau
    (mix_posDef omega _ (maximallyMixed_posDef a ha) t ht ht1.le)
  refine ⟨X, hX, ?_⟩
  have hlo := expectation_mix_lower omega (maximallyMixed a ha) t ht.le ht1.le (L X) (hpos X hX)
  change (1 - t) * expectation L X omega.matrix ≤ expectation L X tau.matrix at hlo
  by_contra hbad
  have hge : s ≤ expectation L X omega.matrix := le_of_not_gt hbad
  have hh := mul_le_mul_of_nonneg_left hge (sub_nonneg.mpr ht1.le)
  exact (not_lt_of_ge (hh.trans hlo)) (hv.trans hgap)

/-- Faithful pointwise costs yield one feasible auxiliary with a uniform norm cost. -/
theorem exists_uniform_marginal_bound_of_faithful (ha : 0 < a)
    (L : Operator n →ₗ[ℝ] Operator a) (T : Set (Operator n)) (hT : Convex ℝ T)
    (hpos : ∀ X ∈ T, (L X).PosSemidef) (r s : ℝ) (hr : 0 ≤ r) (hrs : r < s)
    (hpoint : ∀ omega : State a, omega.matrix.PosDef → ∃ X ∈ T, expectation L X omega.matrix < r) :
    ∃ X ∈ T, ‖L X‖ ≤ s := by
  obtain ⟨u, hru, hus⟩ := exists_between hrs
  exact exists_uniform_marginal_bound (maximallyMixed a ha) L T hT hpos u s hus
    (pointwise_bound_of_faithful ha L T hpos r u hr hru hpoint)

end QuantumChannelStein.PositiveMarginalMinimax
