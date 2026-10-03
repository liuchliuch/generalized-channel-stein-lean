import GeneralizedChannelStein.LocalApproximationFinite
import GeneralizedChannelStein.SiteGrouping

/-! Lemma 27 for an explicitly named physical retained/discarded split. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix LocalExpansion SiteGrouping
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem lemma_27_fixed {a : ℕ} (ha : 0<a) (τ : State a) (t : ℝ) (ht : 0<t) (ht1 : t≤1)
    (hτ : (τ.matrix-t•(1:Operator a)).PosSemidef) (k m : ℕ) (ξ : ℝ)
    (hξ : 0<ξ) (hξ1 : ξ≤1/16) (hn : WeightedDiscardingScalars.blockThreshold a t≤k+m)
    (hmdef : WeightedDiscardingScalars.discardCount ((k+m:ℕ):ℝ) ξ=m)
    (hma : (m:ℝ)≤((k+m:ℕ):ℝ)/2)
    (W : Operator (a^(k+m)))
    (hW : ∀ π : Equiv.Perm (Fin (k+m)), Matrix.reindex (sitePermutation a (k+m) π)
      (sitePermutation a (k+m) π) W=W) (hWn : ‖W‖≤1) :
    ∃ E : Expansion (Fin a) k,
      (∀ i, ((E.sites i).card:ℝ)≤WeightedDiscardingScalars.supportConstant a t*((k+m:ℕ):ℝ)^(2/3:ℝ)) ∧
      E.cost≤Real.exp (WeightedDiscardingScalars.supportConstant a t*((k+m:ℕ):ℝ)^(2/3:ℝ)) ∧
      ‖flatten E.value-finiteWeightedExpectation τ k m W‖≤ξ := by
  have hma' : (WeightedDiscardingScalars.discardCount ((k+m:ℕ):ℝ) ξ:ℝ)≤((k+m:ℕ):ℝ)/2 := by rwa [hmdef]
  have hkdef : Lemma27Parameters.k (k+m) ξ=k := by simp only [Lemma27Parameters.k,Lemma27Parameters.m,hmdef,Nat.add_sub_cancel_right]
  have hmd : Lemma27Parameters.m (k+m) ξ=m := hmdef
  have hr := lemma_27_of_lowerBound ha τ t ht ht1 hτ (k+m) ξ hξ hξ1 hn hma'
    (recursiveOperator W) (recursiveOperator_invariant W hW) (by rwa [norm_recursiveOperator])
  have transport (k' m' : ℕ) (hk' : k'=k) (hm' : m'=m) (hsm : k'+m'=k+m)
      (hr : ∃ E : Expansion (Fin a) k',
        (∀ i, ((E.sites i).card:ℝ)≤WeightedDiscardingScalars.supportConstant a t*((k+m:ℕ):ℝ)^(2/3:ℝ)) ∧
        E.cost≤Real.exp (WeightedDiscardingScalars.supportConstant a t*((k+m:ℕ):ℝ)^(2/3:ℝ)) ∧
        ‖E.value-weightedExpectationSplit τ k' m' hsm (recursiveOperator W)‖≤ξ) :
      ∃ E : Expansion (Fin a) k,
        (∀ i, ((E.sites i).card:ℝ)≤WeightedDiscardingScalars.supportConstant a t*((k+m:ℕ):ℝ)^(2/3:ℝ)) ∧
        E.cost≤Real.exp (WeightedDiscardingScalars.supportConstant a t*((k+m:ℕ):ℝ)^(2/3:ℝ)) ∧
        ‖E.value-weightedExpectation τ k m (recursiveOperator W)‖≤ξ := by
    subst k'; subst m'
    simpa only [weightedExpectationSplit] using hr
  obtain ⟨E,hs,hc,he⟩ := transport _ _ hkdef hmd
    (Lemma27Parameters.paper_parameters ht hξ hξ1 hn hma').split hr
  refine ⟨E,hs,hc,?_⟩
  have hid : flatten (weightedExpectation τ k m (recursiveOperator W))=finiteWeightedExpectation τ k m W := by
    rw [weightedExpectation,finiteWeightedExpectation_eq]
    ext i j
    simp [flatten,encode,Matrix.reindex_apply]
  have hnrm := norm_flatten (E.value-weightedExpectation τ k m (recursiveOperator W))
  have hsub : flatten (E.value-weightedExpectation τ k m (recursiveOperator W)) =
      flatten E.value-flatten (weightedExpectation τ k m (recursiveOperator W)) := rfl
  rw [hsub,hid] at hnrm
  exact hnrm.trans_le he

end GeneralizedChannelStein
