import GeneralizedChannelStein.SeparableStates
import GeneralizedChannelStein.CompactConvexHull

/-! Compactness and all five axioms for the full entanglement-breaking block families. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TestingSDP ChannelPowerReindex PerfectDiscrimination
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

theorem isCompact_separableStateMatrices (a b : ℕ) : IsCompact (separableStateMatrices a b) :=
  CompactConvexHull.isCompact_convexHull (isCompact_productStateMatrices a b)

theorem eb_choi_image (a b n : ℕ) :
    MatrixMap.choi '' EBFamily a b n = channelChoiSet (a^n) (b^n) ∩ {C | Separable C} := by
  apply channelSlice_choi_image
  intro Φ; rfl

theorem eb_choi_image_normalized (ha : 0<a) (hb : 0<b) (n : ℕ) :
    MatrixMap.choi '' EBFamily a b n = channelChoiSet (a^n) (b^n) ∩
      {C | (((a^n:ℕ):ℝ)⁻¹ • C) ∈ separableStateMatrices (a^n) (b^n)} := by
  rw [eb_choi_image]
  ext C
  constructor
  · rintro ⟨hC,hsep⟩
    exact ⟨hC,(separable_fixed_trace_iff (pow_pos ha n) (pow_pos hb n)
      (by exact_mod_cast pow_pos ha n) (by simpa using channelChoiSet_trace hC)).mp hsep⟩
  · rintro ⟨hC,hsep⟩
    exact ⟨hC,(separable_fixed_trace_iff (pow_pos ha n) (pow_pos hb n)
      (by exact_mod_cast pow_pos ha n) (by simpa using channelChoiSet_trace hC)).mpr hsep⟩

theorem isCompact_eb_choi (ha : 0<a) (hb : 0<b) (n : ℕ) :
    IsCompact (MatrixMap.choi '' EBFamily a b n) := by
  rw [eb_choi_image_normalized ha hb]
  apply (isCompact_channelChoiSet _ _).inter_right
  exact (isCompact_separableStateMatrices _ _).isClosed.preimage (continuous_const.smul continuous_id)

theorem eb_admissible (ha : 0<a) (hb : 0<b) (ω : State b) (hω : ω.matrix.PosDef) :
    Admissible (EBFamily a b) where
  channels n hn Φ hΦ := hΦ.1
  nonempty n hn := by
    refine ⟨(ReplacerChannel.channel (a^n) (statePower ω n)).toLinearMap,?_⟩
    exact (mem_EBFamily_iff _ _).mpr (replacer_entanglementBreaking _ _)
  compact n hn := isCompact_eb_choi ha hb n
  convex n hn := by
    rw [eb_choi_image]
    exact (convex_channelChoiSet _ _).inter (convex_separable _ _)
  tensor_closed n m hn hm Φ Ψ hΦ hΨ := by
    apply (mem_EBFamily_iff _ _).mpr
    exact (((mem_EBFamily_iff _ _).mp hΦ).tensor ((mem_EBFamily_iff _ _).mp hΨ)).reindex _ _
  faithful_replacer := by
    refine ⟨ω,hω,⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩⟩
    rw [ReplacerChannel.tensorPower_map,← ReplacerChannel.channel_map,MatrixMap.choi_toLinearMap]
    exact (entanglementBreaking_iff_separable_choi _).mp (replacer_entanglementBreaking _ _)

/-- Proposition 22's complete structural assertion, for any faithful witnesses. -/
theorem proposition_22_families (ha : 0<a) (hb : 0<b)
    (τ : State a) (ω : State b) (hτ : τ.matrix.PosDef) (hω : ω.matrix.PosDef) :
    Admissible (EBFamily a b) ∧ QuantitativeAt (EBFamily a b) τ ∧
    Admissible (PPTFamily a b) ∧ QuantitativeAt (PPTFamily a b) τ :=
  ⟨eb_admissible ha hb ω hω,eb_quantitative τ hτ,ppt_admissible ω hω,ppt_quantitative τ hτ⟩


/-- The cone formulation is exactly the usual formulation on normalized input states. -/
theorem entanglementBreaking_iff_normalized_inputs (Φ : KrausChannel a b) :
    IsEntanglementBreaking Φ ↔ ∀ r, ∀ X : BipartiteOperator r a,
      X.PosSemidef → X.trace=1 → Separable (Φ.amplify r X) := by
  constructor
  · intro h r X hX ht
    exact h r X hX
  · intro h r X hX
    have ht0 : 0≤X.trace.re := (Complex.nonneg_iff.mp hX.trace_nonneg).1
    by_cases ht : 0<X.trace.re
    · let Y := X.trace.re⁻¹ • X
      have hY : Y.PosSemidef := hX.smul (inv_nonneg.mpr ht.le)
      have htr : X.trace=(X.trace.re:ℂ) := by
        apply Complex.ext
        · rfl
        · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp hX.trace_nonneg).2.symm
      have hYtr : Y.trace=1 := by
        change (X.trace.re⁻¹ • X).trace=1
        rw [Matrix.trace_smul,htr,Complex.real_smul,← Complex.ofReal_mul,Complex.ofReal_re,
          inv_mul_cancel₀ ht.ne',Complex.ofReal_one]
      have hs := (h r Y hY hYtr).smul ht.le
      rw [← ChannelEntropy.amplify_real_smul] at hs
      have he : X.trace.re • Y=X := by dsimp [Y]; rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
      rwa [he] at hs
    · have hz : X.trace.re=0 := le_antisymm (le_of_not_gt ht) ht0
      have hnorm := positive_norm_le_trace hX
      rw [hz] at hnorm
      have hX0 : X=0 := norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
      rw [hX0]
      have he : Φ.amplify r (0:BipartiteOperator r a)=0 := by simp [KrausChannel.amplify]
      rw [he]
      exact Separable.zero

end GeneralizedChannelStein
