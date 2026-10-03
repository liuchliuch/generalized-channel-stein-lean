import GeneralizedChannelStein.OverlapFeasibility
import GeneralizedChannelStein.CPTPAEP
import GeneralizedChannelStein.LocalCorrection
import GeneralizedChannelStein.WeightedCorrection
import GeneralizedChannelStein.CompletionLossOrder
import GeneralizedChannelStein.LocalApproximationFixed

/-! Proposition 30: uniform exact-TP completion of an isometric target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace GeneralizedChannelStein.IsometricCompletion
open QuantumChannelStein Matrix ChannelEntropy ChannelPowerReindex PerfectDiscrimination
  LocalExpansion SiteGrouping CompletionPrecision CompletionScalars ExpansionBudget
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a d : ℕ}

def uniformConstant (a d : ℕ) (t w c : ℝ) : ℝ :=
  totalUniformCost (kappa c) (q1 c) (WeightedDiscardingScalars.supportConstant a t)
    (WeightedCorrection.base a d t w) ((d:ℝ)/w) (WeightedDiscardingScalars.blockThreshold a t)

theorem support_constant_nonneg (a : ℕ) (t : ℝ) : 0≤WeightedDiscardingScalars.supportConstant a t := by
  have h := WeightedDiscardingScalars.logConstant_pos a
  unfold WeightedDiscardingScalars.supportConstant WeightedDiscardingScalars.dampingScale
  positivity

theorem replacer_rate_ge_one (hd : 0<d) {w : ℝ} (hw : 0<w) (hw1 : w≤1) : 1≤(d:ℝ)/w := by
  apply (le_div_iff₀ hw).mpr
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  linarith

theorem uniform_bounds (ha : 0<a) (hd : 0<d) {t w c : ℝ}
    (ht : 0<t) (ht1 : t≤1) (hw : 0<w) (hw1 : w≤1) (hc : 0<c) (hc1 : c≤1) :
    0<uniformConstant a d t w c ∧
    uniformCost (kappa c) (q1 c) (WeightedDiscardingScalars.supportConstant a t)
      (WeightedCorrection.base a d t w) ((d:ℝ)/w)≤uniformConstant a d t w c ∧
    fallbackCost (kappa c) ((d:ℝ)/w) (WeightedDiscardingScalars.blockThreshold a t)≤uniformConstant a d t w c := by
  have h := fixed_precision_bounds hc hc1
  exact totalUniformCost_bounds _ h.kappa_pos (by linarith [h.kappa_le])
    (h.q0_nonneg.trans_lt h.q0_lt_q1) h.q1_lt_one (support_constant_nonneg a t)
    (WeightedCorrection.base_ge_one ha hd ht ht1 hw hw1) (replacer_rate_ge_one hd hw hw1)

theorem loss_mono {n : ℕ} {δ K L : ℝ} (hδ : 0<δ) (hδ1 : δ≤1/16) (hKL : K≤L) :
    completionLoss K n δ≤completionLoss L n δ := by
  have hr : 1≤((n:ℝ)+1)/δ := (le_div_iff₀ hδ).mpr (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have hl : 0≤Real.logb 2 (((n:ℝ)+1)/δ) := Real.logb_nonneg (by norm_num) hr
  unfold completionLoss
  gcongr

theorem active (ha : 0<a) (hd : 0<d) (t w c : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hw : 0<w) (hw1 : w≤1) (hc : 0<c) (hc1 : c≤1)
    (F : AlternativeFamily a d) (hF : Admissible F) (τ : State a) (hτ : QuantitativeAt F τ)
    (ω : State d) (hωmem : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (htτ : (τ.matrix-t•(1:Operator a)).PosSemidef) (hwω : (ω.matrix-w•(1:Operator d)).PosSemidef)
    (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (k m : ℕ) (hk : 2≤k) (hm : 0<m)
    (M : KrausChannel (a^(k+m)) (d^(k+m))) (hM : M.toLinearMap∈F (k+m))
    (V : Matrix (Fin (d^(k+m))) (Fin (a^(k+m))) ℂ) (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (hV : ‖V‖≤1) (hcover : (BranchExtraction.realPart ((powerIsometry J (k+m))ᴴ*V)-c•1).PosSemidef)
    (hdom : MatrixMap.CPLe (Complex.ofReal p•BranchExtraction.adMap V) M.toLinearMap)
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1/16)
    (hn : WeightedDiscardingScalars.blockThreshold a t≤k+m)
    (hmdef : WeightedDiscardingScalars.discardCount ((k+m:ℕ):ℝ) (kappa c*δ)=m)
    (hma : (m:ℝ)≤((k+m:ℕ):ℝ)/2) :
    ∃ L S : KrausChannel (a^(k+m)) (d^(k+m)), S.toLinearMap∈F (k+m) ∧
      MatrixMap.CPLe (Complex.ofReal (p*(2:ℝ)^(-completionLoss (uniformConstant a d t w c) (k+m) δ))•L.toLinearMap) S.toLinearMap ∧
      DiamondNorm.diamondNorm (L.toLinearMap-BranchExtraction.adMap (powerIsometry J (k+m)))≤ENNReal.ofReal δ := by
  have hkp : 0<k := by omega
  have hnp : 0<k+m := by omega
  have hparam := fixed_precision_bounds hc hc1
  obtain ⟨hξ,hξ1,hζ⟩ := scaled_precision_bounds hc hc1 hδ hδ1
  let ξ := kappa c*δ
  let ζ := (2*Mc c+1)*ξ
  have hζ0 : 0≤ζ := by dsimp [ζ,ξ]; have hMc := hparam.Mc_pos; positivity
  have hζ1 : ζ<1 := by dsimp [ζ,ξ]; linarith
  let Vb := SymmetrizedBranch.average V
  obtain ⟨Mb,hMb,hDb⟩ := SymmetrizedBranch.average_free_dominator F hF τ hτ hnp M hM V p hp hdom
  have hVb : ‖Vb‖≤1 := SymmetrizedBranch.norm_average V hV
  have hCb : (BranchExtraction.realPart ((powerIsometry J (k+m))ᴴ*Vb)-c•1).PosSemidef :=
    SymmetrizedBranch.average_overlap J (k+m) V c hcover
  let W := (powerIsometry J (k+m))ᴴ*Vb
  have hWi (π : Equiv.Perm (Fin (k+m))) : Matrix.reindex (sitePermutation a (k+m) π)
      (sitePermutation a (k+m) π) W=W := by
    change SymmetrizedBranch.permute π ((powerIsometry J (k+m))ᴴ*Vb)=_
    rw [← SymmetrizedBranch.gram_permute,SymmetrizedBranch.average_invariant]
  have hWn : ‖W‖≤1 := (Matrix.l2_opNorm_mul _ _).trans (by
    rw [Matrix.l2_opNorm_conjTranspose]
    have hJn := BranchExtraction.norm_isometry_le_one _ (powerIsometry_isometry J hJ (k+m))
    nlinarith [norm_nonneg Vb,norm_nonneg (powerIsometry J (k+m))])
  obtain ⟨Z,Mk,hMk,hZn,hZD,hZE⟩ := DiscardedBranch.exists_free_coherent_branch F τ hτ J hJ
    k m hkp Mb hMb Vb hVb p hp.le hDb
  have hCZ : (BranchExtraction.realPart ((powerIsometry J k)ᴴ*Z)-c•1).PosSemidef := by
    rw [hZE]
    exact DiscardedBranch.weighted_overlap_lower τ k m W c hCb
  obtain ⟨E,hEs,hEc,hEe⟩ := lemma_27_fixed ha τ t ht ht1 htτ k m ξ hξ hξ1 hn hmdef hma W hWi hWn
  rw [← hZE] at hEe
  obtain ⟨O,hOs,hOc,hOe⟩ := LocalCorrection.construct ha hd hk J hJ Z hZn c δ hc hc1 hδ hδ1 hCZ E hEe
  have hO0 : O.value≠0 := value_ne_zero_of_close O (powerIsometry J k) Z
    (powerIsometry_isometry J hJ k) ha hζ1 hOe
  let b0 := WeightedCorrection.base a d t w
  let H := weightedCost O b0
  let Hm := max 1 H
  let r := (d:ℝ)/w
  have hb : 1≤b0 := WeightedCorrection.base_ge_one ha hd ht ht1 hw hw1
  have hr : 1≤r := replacer_rate_ge_one hd hw hw1
  have hH : 0<H := weightedCost_pos O hb hO0
  have hHm : 1≤Hm := le_max_left _ _
  have hHm0 : 0<Hm := by linarith
  obtain ⟨Mk',hMk',hDk⟩ := WeightedCorrection.dominated_correction F hF τ hτ ω hωmem ha hd hkp
    t w p ht ht1 hw hw1 hp htτ hwω Mk hMk Z hZD O hO0
  obtain ⟨Sn,hSn,hDn⟩ := CompletionPadding.pad_dominated J hJ F hF ω hωmem w hw hwω k m hkp hm
    Mk' hMk' (flatten O.value*Z) (Hm^2/p) (by positivity) hDk
  let Zn := CompletionPadding.pad J k m (flatten O.value*Z)
  have hZne : ‖Zn-powerIsometry J (k+m)‖≤ζ := (CompletionPadding.pad_error J hJ k m _).trans hOe
  have hcn : 1≤Hm^2/p*r^m := by
    have h1 : 1≤Hm^2/p := (le_div_iff₀ hp).mpr (by nlinarith)
    exact one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ hr)
  have hR : (ReplacerChannel.channel (a^(k+m)) (statePower ω (k+m))).toLinearMap∈F (k+m) := by
    have h := replacer_power_mem F hF.tensor_closed ω hωmem (k+m) hnp
    rw [ReplacerChannel.tensorPower_map] at h
    rwa [ReplacerChannel.channel_map]
  obtain ⟨L,S,hS,hLS,herr⟩ := CloseBranchCompletion.complete_close_branch (F (k+m)) (hF.convex (k+m) hnp)
    (powerIsometry J (k+m)) Zn (powerIsometry_isometry J hJ (k+m)) (pow_pos ha _) Sn hSn
    (statePower ω (k+m)) hR (Hm^2/p*r^m) ζ hcn hζ0 hDn hZne
  have hLS' := FreeAmplification.cpLe_scalar_mono L.toLinearMap S
    (show Hm^2/p*r^m+1≤2*(Hm^2/p*r^m) by linarith) hLS
  have hB : 0≤WeightedDiscardingScalars.supportConstant a t := support_constant_nonneg a t
  have hHbudget : H≤correctionCost (lam c) E.cost (correctionDegree (q1 c) ξ)*
      15^(projectorDegree k ξ)*b0^(correctionDegree (q1 c) ξ*radius E+projectorDegree k ξ) := by
    exact (weightedCost_bound O hb hOs).trans (mul_le_mul_of_nonneg_right hOc (by positivity))
  have hRbound : (radius E:ℝ)≤WeightedDiscardingScalars.supportConstant a t*blockScale (k+m) :=
    radius_le_real E (by have hn0 : 0≤((k+m:ℕ):ℝ) := Nat.cast_nonneg _; unfold blockScale; positivity) hEs
  have hLoss := active_completion_loss hparam.kappa_pos (by linarith [hparam.kappa_le])
    (hparam.q0_nonneg.trans_lt hparam.q0_lt_q1) hparam.q1_lt_one hB hb hr
    hparam.lam_pos.le hparam.lam_le_one E.cost_nonneg hδ hδ1 hnp (Nat.le_add_right k m) hEc hRbound hHbudget
  rw [hmdef] at hLoss
  have hLoss' : 1+2*Real.logb 2 Hm+(m:ℝ)*Real.logb 2 r≤completionLoss (uniformConstant a d t w c) (k+m) δ :=
    hLoss.trans (loss_mono hδ hδ1 (uniform_bounds ha hd ht ht1 hw hw1 hc hc1).2.1)
  refine ⟨L,S,hS,?_,?_⟩
  · apply CompletionLossOrder.domination_at_loss L S p (2*(Hm^2/p*r^m)) _ _ hp hLS' _ hLoss'
    rw [CompletionLossOrder.exp_log_loss Hm r hHm0 (by linarith) m]
    have he : p*(2*(Hm^2/p*r^m))=2*Hm^2*r^m := by field_simp
    exact he.le
  · exact herr.trans (ENNReal.ofReal_le_ofReal (by dsimp [ζ,ξ]; linarith))


theorem fallback (ha : 0<a) (hd : 0<d) (t w c : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hw : 0<w) (hw1 : w≤1) (hc : 0<c) (hc1 : c≤1)
    (F : AlternativeFamily a d) (hF : Admissible F) (ω : State d)
    (hωmem : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (hwω : (ω.matrix-w•(1:Operator d)).PosSemidef)
    (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (n : ℕ) (hn : 0<n) (p : ℝ) (hp : 0<p) (hp1 : p≤1)
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1/16)
    (hbad : n<WeightedDiscardingScalars.blockThreshold a t ∨
      (n:ℝ)/2<(WeightedDiscardingScalars.discardCount n (kappa c*δ):ℝ) ∨
      n-WeightedDiscardingScalars.discardCount n (kappa c*δ)<2) :
    ∃ L S : KrausChannel (a^n) (d^n), S.toLinearMap∈F n ∧
      MatrixMap.CPLe (Complex.ofReal (p*(2:ℝ)^(-completionLoss (uniformConstant a d t w c) n δ))•L.toLinearMap) S.toLinearMap ∧
      DiamondNorm.diamondNorm (L.toLinearMap-BranchExtraction.adMap (powerIsometry J n))≤ENNReal.ofReal δ := by
  let L := BranchExtraction.isometryChannel (powerIsometry J n) (powerIsometry_isometry J hJ n)
  let S := (ReplacerChannel.channel a ω).tensorPower n
  have hparam := fixed_precision_bounds hc hc1
  have hr := replacer_rate_ge_one hd hw hw1
  have hbound := inactive_completion_loss hparam.kappa_pos (by linarith [hparam.kappa_le])
    hδ hδ1 hn hr hbad
  have hbound' : (n:ℝ)*Real.logb 2 ((d:ℝ)/w)≤completionLoss (uniformConstant a d t w c) n δ :=
    hbound.trans (loss_mono hδ hδ1 (uniform_bounds ha hd ht ht1 hw hw1 hc hc1).2.2)
  refine ⟨L,S,replacer_power_mem F hF.tensor_closed ω hωmem n hn,?_,?_⟩
  · apply CompletionLossOrder.domination_at_loss L S p (((d:ℝ)/w)^n) _ _ hp
      (CompletionPadding.isometry_replacer_power J hJ ω w hw hwω n) _ hbound'
    rw [CompletionLossOrder.exp_log_power ((d:ℝ)/w) (by linarith) n]
    exact mul_le_of_le_one_left (pow_nonneg (by linarith) n) hp1
  · have he : L.toLinearMap=BranchExtraction.adMap (powerIsometry J n) := BranchExtraction.isometryChannel_map _ _
    rw [he,sub_self,zero_diamondNorm]
    exact bot_le

/-- Explicit uniform constant for all positive block lengths and accuracies. -/
theorem property_of_le_one (ha : 0<a) (hd : 0<d) (t w c : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hw : 0<w) (hw1 : w≤1) (hc : 0<c) (hc1 : c≤1) :
    IsometricCompletionProperty a d t w c (uniformConstant a d t w c) := by
  refine ⟨(uniform_bounds ha hd ht ht1 hw hw1 hc hc1).1.le,?_⟩
  intro F hF τ hτ ω hωmem htτ hwω J hJ n hn M hM V p hp hp1 hV hcover hdom δ hδ hδ1
  by_cases hN : WeightedDiscardingScalars.blockThreshold a t≤n
  · by_cases hma : (WeightedDiscardingScalars.discardCount n (kappa c*δ):ℝ)≤(n:ℝ)/2
    · by_cases hk : 2≤n-WeightedDiscardingScalars.discardCount n (kappa c*δ)
      · have hparams := Lemma27Parameters.paper_parameters ht
          (scaled_precision_bounds hc hc1 hδ hδ1).1
          (scaled_precision_bounds hc hc1 hδ hδ1).2.1 hN hma
        generalize hmdef : WeightedDiscardingScalars.discardCount n (kappa c*δ)=m at hma hk
        generalize hkdef : n-m=k at hk
        have hmpos : 0<m := by simpa only [Lemma27Parameters.m,hmdef] using hparams.m_pos
        have hmle : m≤n := by
          have hh : (m:ℝ)≤(n:ℝ) := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
          exact_mod_cast hh
        have hsplit : k+m=n := by rw [← hkdef,Nat.sub_add_cancel hmle]
        subst n
        exact active ha hd t w c ht ht1 hw hw1 hc hc1 F hF τ hτ ω hωmem htτ hwω J hJ k m hk hmpos
          M hM V p hp hp1 hV hcover hdom δ hδ hδ1 hN hmdef hma
      · exact fallback ha hd t w c ht ht1 hw hw1 hc hc1 F hF ω hωmem hwω J hJ n hn p hp hp1 δ hδ hδ1
          (Or.inr (Or.inr (by omega)))
    · exact fallback ha hd t w c ht ht1 hw hw1 hc hc1 F hF ω hωmem hwω J hJ n hn p hp hp1 δ hδ hδ1
        (Or.inr (Or.inl (lt_of_not_ge hma)))
  · exact fallback ha hd t w c ht ht1 hw hw1 hc hc1 F hF ω hωmem hwω J hJ n hn p hp hp1 δ hδ hδ1
      (Or.inl (by omega))

/-- Uniform lower-bound version; K precedes every physical witness. -/
theorem proposition_30_lowerBounds (ha : 0<a) (hd : 0<d) {t w c : ℝ}
    (ht : 0<t) (ht1 : t≤1) (hw : 0<w) (hw1 : w≤1) (hc : 0<c) (hc1 : c≤1) :
    ∃ K : ℝ, IsometricCompletionProperty a d t w c K :=
  ⟨uniformConstant a d t w c,property_of_le_one ha hd t w c ht ht1 hw hw1 hc hc1⟩


/-- Full source domain c>0. If c>1 the feasible branch hypotheses are contradictory. -/
theorem proposition_30 (ha : 0<a) (hd : 0<d) {t w c : ℝ}
    (ht : 0<t) (ht1 : t≤1) (hw : 0<w) (hw1 : w≤1) (hc : 0<c) :
    ∃ K : ℝ, IsometricCompletionProperty a d t w c K := by
  by_cases hc1 : c≤1
  · exact proposition_30_lowerBounds ha hd ht ht1 hw hw1 hc hc1
  · refine ⟨0,⟨le_rfl,?_⟩⟩
    intro F hF τ hτ ω hωmem htτ hwω J hJ n hn M hM V p hp hp1 hV hcover hdom δ hδ hδ1
    exact False.elim (hc1 (OverlapFeasibility.feasible_overlap_le_one (powerIsometry J n) V
      (powerIsometry_isometry J hJ n) (pow_pos ha n) hV c hc.le hcover))

end GeneralizedChannelStein.IsometricCompletion
