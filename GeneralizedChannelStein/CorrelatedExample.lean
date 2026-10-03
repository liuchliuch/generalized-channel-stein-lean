import GeneralizedChannelStein.CorrelatedClosure
import GeneralizedChannelStein.RealRates
import GeneralizedChannelStein.IsometricBenchmarks

/-! Example 24: the actual finite partition hull of persistent correlated mixtures. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein.Correlated
open QuantumChannelStein Matrix ChannelPowerReindex PerfectDiscrimination TensorPower ChannelEntropy RelativeEntropy
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
variable {b : ℕ}

/-- The state specialization A=C is represented by its actual trace-and-prepare maps. -/
def alternativeFamily (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) : AlternativeFamily 1 b :=
  fun n => {Φ | ∃ σ : State (b^n), σ.matrix∈partitionHull ρ ω c hc hc1 n ∧
    Φ=ReplacerChannel.linearMap (1^n) σ}

theorem mem_family_of_state (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    (n : ℕ) (σ : State (b^n)) (hσ : σ.matrix∈partitionHull ρ ω c hc hc1 n) :
    (ReplacerChannel.channel (1^n) σ).toLinearMap∈alternativeFamily ρ ω c hc hc1 n :=
  ⟨σ,hσ,ReplacerChannel.channel_map _ _⟩

theorem family_choi_image (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) (n : ℕ) :
    MatrixMap.choi '' alternativeFamily ρ ω c hc hc1 n =
      (fun X : Operator (b^n) => (1:Operator (1^n)) ⊗ₖ X) '' partitionHull ρ ω c hc hc1 n := by
  ext C
  constructor
  · rintro ⟨Φ,⟨σ,hσ,rfl⟩,rfl⟩
    exact ⟨σ.matrix,hσ,(ReplacerChannel.choi_linearMap _ _).symm⟩
  · rintro ⟨X,hX,rfl⟩
    have hd := partitionHull_density ρ ω c hc hc1 n hX
    let σ : State (b^n) := ⟨X,hd.1,hd.2⟩
    refine ⟨ReplacerChannel.linearMap (1^n) σ,⟨σ,hX,rfl⟩,?_⟩
    exact ReplacerChannel.choi_linearMap _ _

theorem family_compact (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) (n : ℕ) :
    IsCompact (MatrixMap.choi '' alternativeFamily ρ ω c hc hc1 n) := by
  rw [family_choi_image]
  apply (partitionHull_compact ρ ω c hc hc1 n).image
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  change Continuous (fun X : Operator (b^n) => (1:Operator (1^n)) i.1 j.1*X i.2 j.2)
  fun_prop

theorem family_convex (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) (n : ℕ) :
    Convex ℝ (MatrixMap.choi '' alternativeFamily ρ ω c hc hc1 n) := by
  rw [family_choi_image]
  intro C hC D hD r s hr hs hrs
  obtain ⟨X,hX,rfl⟩ := hC
  obtain ⟨Y,hY,rfl⟩ := hD
  refine ⟨r • X+s • Y,(convex_convexHull ℝ _) hX hY hr hs hrs,?_⟩
  ext i j
  simp [mul_add]
  ring

/-- Reindexing a replacer changes only its prepared output state. -/
theorem reindex_replacer_map {a d a' d' : ℕ} (ea : Fin a ≃ Fin a') (ed : Fin d ≃ Fin d')
    (Φ : KrausChannel a d) (σ : State d) (hΦ : Φ.toLinearMap=ReplacerChannel.linearMap a σ) :
    (reindexChannel ea ed Φ).toLinearMap=ReplacerChannel.linearMap a' (σ.reindex ed) := by
  ext X i j
  change (reindexChannel ea ed Φ).apply X i j=_
  rw [reindexChannel_apply_any]
  change (Matrix.reindex ed ed (Φ.toLinearMap (Matrix.reindex ea.symm ea.symm X))) i j=_
  rw [hΦ]
  change (Matrix.reindex ed ed ((Matrix.reindex ea.symm ea.symm X).trace • σ.matrix)) i j=_
  rw [trace_reindex_equiv]
  rfl

/-- The physical insertion/discard operation on a replacer is the output marginal. -/
theorem marginal_replacer_map {a : ℕ} (n : ℕ) (τ : State a)
    (Φ : KrausChannel (a^(n+1)) (b^(n+1))) (σ : State (b^(n+1)))
    (hΦ : Φ.toLinearMap=ReplacerChannel.linearMap (a^(n+1)) σ) :
    (marginalChannel n τ Φ).toLinearMap=ReplacerChannel.linearMap (a^n) (discardState n σ) := by
  have he := reindex_replacer_map (channelAddEquiv a n 1).symm (channelAddEquiv b n 1).symm Φ σ hΦ
  ext X i j
  change (marginalChannel n τ Φ).apply X i j=_
  simp only [marginalChannel,KrausChannel.compose_apply]
  change (discardRight (b^n) (b^1)).toLinearMap
    ((reindexChannel _ _ Φ).toLinearMap ((appendState _ _).apply X)) i j=_
  rw [he]
  change (discardRight (b^n) (b^1)).toLinearMap
    (((appendState _ _).apply X).trace • (σ.reindex (channelAddEquiv b n 1).symm).matrix) i j=_
  rw [KrausChannel.trace_apply,map_smul]
  rfl

theorem omega_power_mem (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) (n : ℕ) (hn : 0<n) :
    ((ReplacerChannel.channel 1 ω).tensorPower n).toLinearMap∈alternativeFamily ρ ω c hc hc1 n := by
  refine ⟨statePower ω n,?_,ReplacerChannel.tensorPower_map ω n⟩
  apply subset_convexHull
  obtain ⟨d,hd⟩ := omega_power_generator ρ ω c hc hc1 n hn
  exact ⟨d,congrArg State.matrix hd⟩

theorem family_admissible (ρ ω : State b) (hω : ω.matrix.PosDef)
    (c : ℝ) (hc : 0≤c) (hc1 : c≤1) : Admissible (alternativeFamily ρ ω c hc hc1) where
  channels n hn Φ hΦ := by
    obtain ⟨σ,hσ,rfl⟩ := hΦ
    exact (isChannel_iff_kraus _).mpr ⟨ReplacerChannel.channel _ σ,ReplacerChannel.channel_map _ _⟩
  nonempty n hn := ⟨_,omega_power_mem ρ ω c hc hc1 n hn⟩
  compact n hn := family_compact ρ ω c hc hc1 n
  convex n hn := family_convex ρ ω c hc hc1 n
  tensor_closed n m hn hm Φ Ψ hΦ hΨ := by
    obtain ⟨σ,hσ,hΦ⟩ := hΦ
    obtain ⟨υ,hυ,hΨ⟩ := hΨ
    refine ⟨(σ.tensor υ).reindex (channelAddEquiv b n m),hull_tensor ρ ω c hc hc1 n m hσ hυ,?_⟩
    exact reindex_replacer_map _ _ (Φ.tensor Ψ) (σ.tensor υ)
      (ReplacerChannel.tensor_map_of Φ Ψ σ υ hΦ hΨ)
  faithful_replacer := ⟨ω,hω,omega_power_mem ρ ω c hc hc1 1 (by norm_num)⟩

theorem family_quantitative (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1) :
    QuantitativeAt (alternativeFamily ρ ω c hc hc1) scalarState where
  faithful := Matrix.PosDef.one
  permutation_closed n hn π Φ hΦ := by
    obtain ⟨σ,hσ,hΦ⟩ := hΦ
    refine ⟨σ.reindex (sitePermutation b n π),hull_permutation ρ ω c hc hc1 n π hσ,?_⟩
    exact reindex_replacer_map _ _ Φ σ hΦ
  marginal_closed n hn Φ hΦ := by
    obtain ⟨σ,hσ,hΦ⟩ := hΦ
    exact ⟨discardState n σ,hull_marginal ρ ω c hc hc1 n hσ,marginal_replacer_map n scalarState Φ σ hΦ⟩


/-- A one-copy coordinate transport recovers the original density operator. -/
theorem statePower_one_reindex (ρ : State b) :
    (statePower ρ 1).reindex (finCongr (Nat.pow_one b))=ρ := by
  rw [StatePowerRenyi.statePower_succ ρ 0]
  have hz : statePower ρ 0=scalarState := ParallelBlockTests.state_one_unique _ _
  rw [hz]
  apply State.eq_of_matrix_eq
  have h := reindex_tensor_one ρ.matrix
  simpa only [State.reindex_matrix,State.tensor_matrix,scalarState,Matrix.reindex_apply,
    Matrix.submatrix_submatrix] using h

theorem statePower_one_ne (ρ ω : State b) (hne : ρ≠ω) : (statePower ρ 1).matrix≠(statePower ω 1).matrix := by
  intro h
  have hs := State.eq_of_matrix_eq h
  have ht := congrArg (fun σ : State (b^1) => σ.reindex (finCongr (Nat.pow_one b))) hs
  dsimp only at ht
  rw [statePower_one_reindex,statePower_one_reindex] at ht
  exact hne ht

/-- At one site the hull is contained in the segment with target weight at most c. -/
theorem one_site_hull_segment (ρ ω : State b) (c : ℝ) (hc : 0≤c) (hc1 : c≤1)
    {X : Operator (b^1)} (hX : X∈partitionHull ρ ω c hc hc1 1) :
    ∃ t : ℝ, 0≤t ∧ t≤c ∧ X=t • (statePower ρ 1).matrix+(1-t) • (statePower ω 1).matrix := by
  apply (convexHull_min ?_ ?_) hX
  · rintro X ⟨d,rfl⟩
    have hf : d.1=(fun _ : Fin 1 => 0) := by funext i; exact Subsingleton.elim _ _
    refine ⟨blockProbability c d.2 0,blockProbability_nonneg c hc d.2 0,?_,?_⟩
    · unfold blockProbability; split_ifs <;> linarith
    · change (partitionState ρ ω 1 d.1 _ _ _).matrix=_
      rw [hf,partitionState_constant]
  · intro X hX Y hY r s hr hs hrs
    obtain ⟨t,ht,htc,hX⟩ := hX
    obtain ⟨u,hu,huc,hY⟩ := hY
    refine ⟨r*t+s*u,by positivity,?_,?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left htc hr,mul_le_mul_of_nonneg_left huc hs]
    · rw [hX,hY]
      have hs' : s=1-r := by linarith
      rw [hs']
      module

theorem target_not_one_site_hull (ρ ω : State b) (hne : ρ≠ω) (c : ℝ) (hc : 0≤c) (hc1 : c<1) :
    (statePower ρ 1).matrix∉partitionHull ρ ω c hc hc1.le 1 := by
  intro h
  obtain ⟨t,ht,htc,he⟩ := one_site_hull_segment ρ ω c hc hc1.le h
  have ht1 : 1-t≠0 := by linarith
  have hz : (1-t) • ((statePower ρ 1).matrix-(statePower ω 1).matrix)=0 := by
    calc
      _ = (statePower ρ 1).matrix-(t • (statePower ρ 1).matrix+(1-t) • (statePower ω 1).matrix) := by module
      _ = 0 := by rw [←he,sub_self]
  have heq := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left ht1)
  exact statePower_one_ne ρ ω hne heq

/-- The actual one-use target channel is outside the one-use free set. -/
theorem target_not_free_one (ρ ω : State b) (hne : ρ≠ω) (c : ℝ) (hc : 0≤c) (hc1 : c<1) :
    ((ReplacerChannel.channel 1 ρ).tensorPower 1).toLinearMap∉alternativeFamily ρ ω c hc hc1.le 1 := by
  rintro ⟨σ,hσ,he⟩
  rw [ReplacerChannel.tensorPower_map] at he
  have ht := congrArg (fun Φ : MatrixMap (1^1) (b^1) => Φ (statePower scalarState 1).matrix) he
  change (statePower scalarState 1).matrix.trace • (statePower ρ 1).matrix =
    (statePower scalarState 1).matrix.trace • σ.matrix at ht
  rw [(statePower scalarState 1).trace_one,one_smul,one_smul] at ht
  rw [←ht] at hσ
  exact target_not_one_site_hull ρ ω hne c hc hc1 hσ

/-- A concrete free alternative contains the target product component at every positive length. -/
theorem persistent_free_dominator (ρ ω : State b) (c : ℝ) (hc : 0<c) (hc1 : c≤1)
    (n : ℕ) (hn : 0<n) :
    ∃ M : KrausChannel (1^n) (b^n), M.toLinearMap∈alternativeFamily ρ ω c hc.le hc1 n ∧
      MatrixMap.CPLe ((ReplacerChannel.channel 1 ρ).tensorPower n).toLinearMap (((c⁻¹:ℝ):ℂ) • M.toLinearMap) := by
  obtain ⟨d,hd⟩ := zeta_generator ρ ω c hc.le hc1 n hn
  let σ := partitionGenerator ρ ω c hc.le hc1 n d
  let M := ReplacerChannel.channel (1^n) σ
  refine ⟨M,mem_family_of_state ρ ω c hc.le hc1 n σ (subset_convexHull _ _ ⟨d,rfl⟩),?_⟩
  apply (MatrixMap.cpLe_iff_choi_difference _ _).mpr
  rw [MatrixMap.choi_smul,ReplacerChannel.tensorPower_map,ReplacerChannel.choi_linearMap]
  change (((c⁻¹:ℝ):ℂ) • M.choi-(1:Operator (1^n)) ⊗ₖ (statePower ρ n).matrix).PosSemidef
  rw [ReplacerChannel.channel_choi]
  have hstate : (c⁻¹ • σ.matrix-(statePower ρ n).matrix).PosSemidef := by
    have he : c⁻¹ • σ.matrix-(statePower ρ n).matrix =
        (c⁻¹*(1-c)) • (statePower ω n).matrix := by
      change c⁻¹ • (partitionGenerator ρ ω c hc.le hc1 n d).matrix-_=_
      rw [hd,smul_add,smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
      module
    rw [he]
    exact (statePower ω n).positive.smul (mul_nonneg (inv_nonneg.mpr hc.le) (sub_nonneg.mpr hc1))
  convert MatrixMap.posSemidef_kronecker (Matrix.PosSemidef.one (n:=Fin (1^n)) (R:=ℂ)) hstate using 1
  ext i j
  simp [Complex.real_smul,mul_sub]
  ring


theorem persistent_entropy_bounds (ρ ω : State b) (c : ℝ) (hc : 0<c) (hc1 : c≤1)
    (n : ℕ) (hn : 0<n) :
    0≤familyEntropy ((ReplacerChannel.channel 1 ρ).tensorPower n) (alternativeFamily ρ ω c hc.le hc1 n) ∧
    familyEntropy ((ReplacerChannel.channel 1 ρ).tensorPower n) (alternativeFamily ρ ω c hc.le hc1 n) ≤
      (Real.logb 2 (1/c):EReal) := by
  obtain ⟨M,hM,hdom⟩ := persistent_free_dominator ρ ω c hc hc1 n hn
  refine ⟨familyEntropy_nonneg _ (by positivity) _,?_⟩
  have hci : 1≤c⁻¹ := (one_le_inv₀ hc).mpr hc1
  simpa only [one_div] using (familyEntropy_le _ M _ hM).trans
    (channelD_le_log2_of_cpLe _ M c⁻¹ hci hdom)

theorem persistent_beta_lower (ρ ω : State b) (c : ℝ) (hc : 0<c) (hc1 : c≤1)
    (n : ℕ) (hn : 0<n) (ε : ℝ) :
    ENNReal.ofReal (c*(1-ε))≤compositeBeta ((ReplacerChannel.channel 1 ρ).tensorPower n)
      (alternativeFamily ρ ω c hc.le hc1 n) ε := by
  obtain ⟨M,hM,hdom⟩ := persistent_free_dominator ρ ω c hc hc1 n hn
  apply le_iInf
  intro t
  have hh := test_acceptance_le_domination _ M c⁻¹ hdom t.val
  have hp := mul_le_mul_of_nonneg_left (t.property.trans hh) hc.le
  rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] at hp
  exact (ENNReal.ofReal_le_ofReal hp).trans (acceptance_le_worst _ t.val M hM)

/-- The canonical operational rate vanishes, despite exclusion at one use. -/
theorem correlated_steinRate_zero (ρ ω : State b) (hb : 0<b) (hω : ω.matrix.PosDef)
    (c : ℝ) (hc : 0<c) (hc1 : c≤1) :
    steinRate (ReplacerChannel.channel 1 ρ) (alternativeFamily ρ ω c hc.le hc1)=0 := by
  let N := ReplacerChannel.channel 1 ρ
  let F := alternativeFamily ρ ω c hc.le hc1
  have hF := family_admissible ρ ω hω c hc.le hc1
  have hlim := testing_limit N (by norm_num) hb F hF (1/2) (by norm_num) (by norm_num)
  have hconst : Filter.Tendsto (fun n : ℕ => (-Real.logb 2 (c*(1-(1/2:ℝ))))/(n:ℝ))
      Filter.atTop (𝓝 0) := Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hle : ∀ᶠ n : ℕ in Filter.atTop,
      testingRateReal N F (1/2) n≤(-Real.logb 2 (c*(1-(1/2:ℝ))))/(n:ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop (0:ℕ)] with n hn
    have hbeta := persistent_beta_lower ρ ω c hc hc1 n hn (1/2)
    have hup := compositeBeta_le_one_sub (N.tensorPower n) (by positivity) (F n) (1/2) (by norm_num) (by norm_num)
    have htop : compositeBeta (N.tensorPower n) (F n) (1/2)≠⊤ := ne_of_lt (hup.trans_lt ENNReal.ofReal_lt_top)
    have hlower : c*(1-(1/2:ℝ))≤(compositeBeta (N.tensorPower n) (F n) (1/2)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal htop).mp hbeta
    have hpos : 0<c*(1-(1/2:ℝ)) := by positivity
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hpos hlower
    exact div_le_div_of_nonneg_right (neg_le_neg hlog) (Nat.cast_nonneg n)
  exact le_antisymm (le_of_tendsto_of_tendsto hlim hconst hle) (steinRate_nonneg N (by norm_num) F)

/-- Example 24. In fact, the construction and nonfaithfulness work for any distinct
rho and omega; the paper's pure rho is a special case. -/
theorem example_24 (ρ ω : State b) (hne : ρ≠ω) (hb : 0<b) (hω : ω.matrix.PosDef)
    (c : ℝ) (hc : 0<c) (hc1 : c<1) :
    Admissible (alternativeFamily ρ ω c hc.le hc1.le) ∧
    QuantitativeAt (alternativeFamily ρ ω c hc.le hc1.le) scalarState ∧
    ((ReplacerChannel.channel 1 ρ).tensorPower 1).toLinearMap∉alternativeFamily ρ ω c hc.le hc1.le 1 ∧
    (∀ n, 0<n → 0≤familyEntropy ((ReplacerChannel.channel 1 ρ).tensorPower n)
      (alternativeFamily ρ ω c hc.le hc1.le n) ∧
      familyEntropy ((ReplacerChannel.channel 1 ρ).tensorPower n) (alternativeFamily ρ ω c hc.le hc1.le n)≤
        (Real.logb 2 (1/c):EReal)) ∧
    (∀ n, 0<n → ∀ ε : ℝ, ENNReal.ofReal (c*(1-ε))≤
      compositeBeta ((ReplacerChannel.channel 1 ρ).tensorPower n) (alternativeFamily ρ ω c hc.le hc1.le n) ε) ∧
    steinRate (ReplacerChannel.channel 1 ρ) (alternativeFamily ρ ω c hc.le hc1.le)=0 := by
  exact ⟨family_admissible ρ ω hω c hc.le hc1.le,family_quantitative ρ ω c hc.le hc1.le,
    target_not_free_one ρ ω hne c hc.le hc1,persistent_entropy_bounds ρ ω c hc hc1.le,
    persistent_beta_lower ρ ω c hc hc1.le,correlated_steinRate_zero ρ ω hb hω c hc hc1.le⟩

end GeneralizedChannelStein.Correlated
