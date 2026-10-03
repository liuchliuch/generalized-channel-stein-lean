import GeneralizedChannelStein.EntropyMinimaxLimit

/-! # Finite coordinates and a uniform gap for a regularized infimum

This generic order lemma retains infinity in the unregularized function.
Only its infimum is made finite by the explicitly supplied finite anchor.
-/
noncomputable section
namespace GeneralizedChannelStein.EntropyInfimumGap

/-- Restricting to actual regularized points and an additive pointwise error
bounds the real infimum gap, even if some original values are infinite. -/
theorem infimum_gap_of_regularization {Y : Type*} [Nonempty Y]
    (f : Y → EReal) (g : Y → ℝ) (r : Y → Y) (B ε : ℝ)
    (hf : ∀ y, 0 ≤ f y) (_hB : 0 ≤ B)
    (hanchor : ∃ y₀, f y₀ ≤ (B:EReal))
    (hg : ∀ y, 0 ≤ g y) (_hε : 0 ≤ ε)
    (heq : ∀ y, (g y:EReal)=f (r y))
    (hbound : ∀ y, (g y:EReal) ≤ f y+(ε:EReal)) :
    (⨅ y, f y) ≠ ⊤ ∧ (⨅ y, f y) ≠ ⊥ ∧
      0 ≤ (⨅ y, g y)-(⨅ y, f y).toReal ∧
      (⨅ y, g y)-(⨅ y, f y).toReal ≤ ε := by
  have hf0 : 0 ≤ ⨅ y, f y := le_iInf hf
  obtain ⟨y₀,hy₀⟩ := hanchor
  have hftop : (⨅ y, f y) ≠ ⊤ :=
    ne_of_lt (((iInf_le f y₀).trans hy₀).trans_lt (EReal.coe_lt_top B))
  have hfbot : (⨅ y, f y) ≠ ⊥ := ne_of_gt (EReal.bot_lt_zero.trans_le hf0)
  have hfinite := EReal.coe_toReal hftop hfbot
  have hgbdd : BddBelow (Set.range g) := ⟨0,by rintro _ ⟨y,rfl⟩; exact hg y⟩
  have hlo : (⨅ y, f y).toReal ≤ ⨅ y, g y := by
    apply le_ciInf
    intro y
    apply EReal.coe_le_coe_iff.mp
    rw [hfinite,heq]
    exact iInf_le f (r y)
  have hu : (((⨅ y, g y)-ε:ℝ):EReal) ≤ ⨅ y, f y := by
    apply le_iInf
    intro y
    by_cases hytop : f y=⊤
    · rw [hytop]; exact le_top
    have hybot : f y≠⊥ := ne_of_gt (EReal.bot_lt_zero.trans_le (hf y))
    have hyfinite := EReal.coe_toReal hytop hybot
    have hb := hbound y
    rw [← hyfinite,← EReal.coe_add] at hb
    have hb' := EReal.coe_le_coe_iff.mp hb
    rw [← hyfinite]
    apply EReal.coe_le_coe_iff.mpr
    have hi := ciInf_le hgbdd y
    linarith
  rw [← hfinite] at hu
  have hu' := EReal.coe_le_coe_iff.mp hu
  exact ⟨hftop,hfbot,sub_nonneg.mpr hlo,by linarith⟩

end GeneralizedChannelStein.EntropyInfimumGap
