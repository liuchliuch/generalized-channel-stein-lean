import GeneralizedChannelStein.DominatedEntropyContinuity

/-! # A finite-game limit passage with actual maximum attainment

This is a generic optimization lemma. Its approximation and finite-game
bounds must be discharged by the quantum application; they are not a
statement of the final channel minimax theorem.
-/
noncomputable section
namespace GeneralizedChannelStein.EntropyMinimaxLimit

/-- Uniform linear-error approximations only on (0,1) already imply continuity. -/
theorem continuous_of_uniform_linear_error_Ioo {X : Type*} [TopologicalSpace X]
    (g : X → ℝ) (gδ : ℝ → X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcont : ∀ δ : ℝ, 0 < δ → δ < 1 → Continuous (gδ δ))
    (herr : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ x, |gδ δ x-g x| ≤ δ*C) :
    Continuous g := by
  apply DominatedEntropyContinuity.continuous_of_uniform_linear_error g
    (fun t => gδ (min t (1/2))) C hC
  · intro t ht
    exact hcont _ (lt_min ht (by norm_num)) ((min_le_right _ _).trans_lt (by norm_num))
  · intro t ht x
    have he := herr (min t (1/2)) (lt_min ht (by norm_num))
      ((min_le_right _ _).trans_lt (by norm_num)) x
    exact he.trans (by nlinarith [min_le_left t (1/2)])

/-- The exact continuous limiting game attains the finite minimax value.
The lower bound on regularized suprema is retained as an explicit entrance. -/
theorem regularized_minimax_attained {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X]
    (g : X → ℝ) (gδ : ℝ → X → ℝ) (E C : ℝ) (hC : 0 ≤ C)
    (hcont : ∀ δ : ℝ, 0 < δ → δ < 1 → Continuous (gδ δ))
    (herr : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ x, |gδ δ x-g x| ≤ δ*C)
    (hweak : ∀ x, g x ≤ E)
    (hregularized : ∀ δ : ℝ, 0 < δ → δ < 1 → E ≤ ⨆ x, gδ δ x) :
    Continuous g ∧ (⨆ x, g x)=E ∧ ∃ x, g x=E := by
  have hg := continuous_of_uniform_linear_error_Ioo g gδ C hC hcont herr
  obtain ⟨x,hx,hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hg.continuousOn
  have hmax' (y : X) : g y ≤ g x := hmax (Set.mem_univ y)
  have heq : g x=E := by
    apply le_antisymm (hweak x)
    by_contra! hlt
    let δ := min (1/2) ((E-g x)/(2*(C+1)))
    have hδ : 0 < δ := lt_min (by norm_num) (div_pos (sub_pos.mpr hlt) (by positivity))
    have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hsmall : δ*(2*(C+1)) ≤ E-g x :=
      (le_div_iff₀ (show (0:ℝ)<2*(C+1) by positivity)).mp (min_le_right _ _)
    have hb : (⨆ y, gδ δ y) ≤ g x+δ*C := by
      apply ciSup_le
      intro y
      have he := (abs_le.mp (herr δ hδ hδ1 y)).2
      have hy := hmax' y
      linarith
    have hE := (hregularized δ hδ hδ1).trans hb
    nlinarith
  refine ⟨hg,?_,x,heq⟩
  apply le_antisymm (ciSup_le hweak)
  rw [← heq]
  exact le_ciSup ⟨E,by rintro _ ⟨y,rfl⟩; exact hweak y⟩ x

end GeneralizedChannelStein.EntropyMinimaxLimit
