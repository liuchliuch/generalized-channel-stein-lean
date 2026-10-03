import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Compact convex hulls from genuine bounded-card Carathéodory representations -/
noncomputable section
namespace GeneralizedChannelStein.CompactConvexHull
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual convex combinations of exactly k slots, allowing zero weights and repeated points. -/
def combinations (K : Set E) (k : ℕ) : Set E :=
  (fun p : (Fin k → ℝ) × (Fin k → E) => ∑ i, p.1 i • p.2 i) ''
    (stdSimplex ℝ (Fin k) ×ˢ Set.pi Set.univ (fun _ : Fin k => K))

omit [FiniteDimensional ℝ E] in
theorem isCompact_combinations {K : Set E} (hK : IsCompact K) (k : ℕ) :
    IsCompact (combinations K k) := by
  apply ((isCompact_stdSimplex ℝ (Fin k)).prod (isCompact_univ_pi fun _ : Fin k => hK)).image
  apply continuous_finset_sum
  intro i hi
  exact ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)

omit [FiniteDimensional ℝ E] in
theorem combinations_subset_convexHull (K : Set E) (k : ℕ) :
    combinations K k ⊆ convexHull ℝ K := by
  rintro x ⟨⟨w,z⟩,⟨hw,hz⟩,rfl⟩
  apply (convex_convexHull ℝ K).sum_mem (fun i _ => hw.1 i) hw.2
  intro i hi
  exact subset_convexHull ℝ K (hz i (Set.mem_univ i))

/-- Every actual hull point uses at most finrank+1 slots, without an assumed
finite-dimensional hull representation. -/
theorem exists_bounded_combination {K : Set E} {x : E} (hx : x ∈ convexHull ℝ K) :
    ∃ k : ℕ, k ≤ Module.finrank ℝ E + 1 ∧ x ∈ combinations K k := by
  classical
  obtain ⟨ι, hι, z, w, hz, hind, hw, hsum, hxsum⟩ := eq_pos_convex_span_of_mem_convexHull hx
  letI := hι
  have hn : Nonempty ι := by
    by_contra hn
    letI : IsEmpty ι := not_nonempty_iff.mp hn
    simp at hsum
  letI := hn
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
    rw [← hind.finrank_vectorSpan_add_one]
    exact Nat.add_le_add_right (Submodule.finrank_le _) 1
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, hcard, ?_⟩
  refine ⟨((fun i => w (e.symm i)), (fun i => z (e.symm i))), ⟨?_,?_⟩, ?_⟩
  · refine ⟨fun i => (hw (e.symm i)).le, ?_⟩
    exact (Equiv.sum_comp e.symm w).trans hsum
  · intro i hi
    exact hz ⟨e.symm i,rfl⟩
  · exact (Equiv.sum_comp e.symm (fun i => w i • z i)).trans hxsum

/-- Exact bounded-union form of the finite-dimensional convex hull. -/
theorem convexHull_eq_finite_union (K : Set E) :
    convexHull ℝ K = ⋃ k ∈ Finset.range (Module.finrank ℝ E + 2), combinations K k := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨k,hk,hxk⟩ := exists_bounded_combination hx
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),hxk⟩⟩
  · apply Set.iUnion_subset
    intro k
    apply Set.iUnion_subset
    intro hk
    exact combinations_subset_convexHull K k

/-- In a finite-dimensional real normed space, the convex hull of every compact
set is compact. Empty sets and zero-dimensional spaces are included. -/
theorem isCompact_convexHull {K : Set E} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  rw [convexHull_eq_finite_union]
  exact (Finset.range (Module.finrank ℝ E + 2)).finite_toSet.isCompact_biUnion
    (fun k hk => isCompact_combinations hK k)

/-- Closedness is a consequence of the actual compact-hull construction. -/
theorem isClosed_convexHull {K : Set E} (hK : IsCompact K) :
    IsClosed (convexHull ℝ K) := (isCompact_convexHull hK).isClosed

/-- Explicit bounded finite barycentric data, convenient for operational expansions. -/
theorem exists_convex_sum {K : Set E} {x : E} (hx : x ∈ convexHull ℝ K) :
    ∃ k : ℕ, k ≤ Module.finrank ℝ E + 1 ∧
      ∃ w : Fin k → ℝ, ∃ z : Fin k → E,
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
          (∀ i, z i ∈ K) ∧ (∑ i, w i • z i = x) := by
  obtain ⟨k,hk,⟨⟨w,z⟩,⟨hw,hz⟩,heq⟩⟩ := exists_bounded_combination hx
  exact ⟨k,hk,w,z,hw.1,hw.2,fun i => hz i (Set.mem_univ _),heq⟩

end GeneralizedChannelStein.CompactConvexHull
