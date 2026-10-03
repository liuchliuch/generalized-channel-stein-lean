import GeneralizedChannelStein.QuantitativeFamilies
import GeneralizedChannelStein.ChannelSpace
import GeneralizedChannelStein.CompositeTesting
import QuantumChannelStein.ParallelTestingAttainment

/-! Proposition 19: actual channels preserving tensor powers of fixed reference states. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelPowerReindex PerfectDiscrimination Matrix
open scoped BigOperators Kronecker ComplexOrder

variable {a b : ℕ}

/-- The full state-preserving family, not merely product channels. -/
def statePreservingFamily (τ : State a) (ω : State b) : AlternativeFamily a b :=
  fun n => preservingSet (statePower τ n) (statePower ω n)

/-- State tensor powers respect the same block concatenation as channel powers. -/
theorem statePower_add_matrix {d : ℕ} (ρ : State d) (n m : ℕ) :
    Matrix.reindex (channelAddEquiv d n m) (channelAddEquiv d n m)
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((statePower ρ n).matrix ⊗ₖ (statePower ρ m).matrix)) =
      (statePower ρ (n+m)).matrix := by
  have h := TensorPower.tensorPower_add_reindex ρ.matrix n m
  ext i j
  simpa [statePower,channelAddEquiv,channelConcatEquiv,Matrix.reindex_apply] using
    congrFun (congrFun h ((channelIndexEquiv d (n+m)).symm i))
      ((channelIndexEquiv d (n+m)).symm j)

theorem replacer_preserving (τ : State a) (ω : State b) :
    (ReplacerChannel.channel a ω).toLinearMap ∈ preservingSet τ ω := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  change (ReplacerChannel.channel a ω).apply τ.matrix = ω.matrix
  rw [ReplacerChannel.channel_apply,τ.trace_one,one_smul]

theorem replacer_power_preserving (τ : State a) (ω : State b) (n : ℕ) :
    ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ statePreservingFamily τ ω n := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  rw [ReplacerChannel.tensorPower_map]
  change (statePower τ n).matrix.trace • (statePower ω n).matrix = _
  rw [(statePower τ n).trace_one,one_smul]

theorem statePreserving_tensor (τ : State a) (ω : State b) (n m : ℕ)
    (Φ : KrausChannel (a^n) (b^n)) (Ψ : KrausChannel (a^m) (b^m))
    (hΦ : Φ.toLinearMap ∈ statePreservingFamily τ ω n)
    (hΨ : Ψ.toLinearMap ∈ statePreservingFamily τ ω m) :
    (tensorBlocks n m Φ Ψ).toLinearMap ∈ statePreservingFamily τ ω (n+m) := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  change (tensorBlocks n m Φ Ψ).apply (statePower τ (n+m)).matrix = _
  rw [← statePower_add_matrix τ n m]
  unfold tensorBlocks
  rw [reindexChannel_apply,KrausChannel.tensor_apply_product]
  change Matrix.reindex _ _ (Matrix.reindex _ _
    (Φ.toLinearMap (statePower τ n).matrix ⊗ₖ Ψ.toLinearMap (statePower τ m).matrix)) = _
  rw [hΦ.2,hΨ.2,statePower_add_matrix]

/-- All three basic conditions are proved for the literal affine constraint. -/
theorem statePreserving_admissible (τ : State a) (ω : State b) (hω : ω.matrix.PosDef) :
    Admissible (statePreservingFamily τ ω) where
  channels n hn Φ hΦ := hΦ.1
  nonempty n hn := ⟨_,replacer_power_preserving τ ω n⟩
  compact n hn := isCompact_preservingSet_choi _ _
  convex n hn := convex_preservingSet_choi _ _
  tensor_closed n m hn hm Φ Ψ hΦ hΨ := statePreserving_tensor τ ω n m Φ Ψ hΦ hΨ
  faithful_replacer := ⟨ω,hω,replacer_power_preserving τ ω 1⟩

theorem statePreserving_permutation (τ : State a) (ω : State b) (n : ℕ)
    (π : Equiv.Perm (Fin n)) (Φ : KrausChannel (a^n) (b^n))
    (hΦ : Φ.toLinearMap ∈ statePreservingFamily τ ω n) :
    (permuteChannel n π Φ).toLinearMap ∈ statePreservingFamily τ ω n := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  change (permuteChannel n π Φ).apply (statePower τ n).matrix = _
  rw [← statePower_permutation τ n π]
  unfold permuteChannel
  rw [reindexChannel_apply]
  change Matrix.reindex _ _ (Φ.toLinearMap (statePower τ n).matrix) = _
  rw [hΦ.2,statePower_permutation]

theorem statePreserving_marginal (τ : State a) (ω : State b) (n : ℕ)
    (Φ : KrausChannel (a^(n+1)) (b^(n+1)))
    (hΦ : Φ.toLinearMap ∈ statePreservingFamily τ ω (n+1)) :
    (marginalChannel n τ Φ).toLinearMap ∈ statePreservingFamily τ ω n := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  change (marginalChannel n τ Φ).apply (statePower τ n).matrix = _
  simp only [marginalChannel,KrausChannel.compose_apply,appendState_apply]
  let X := Matrix.reindex finProdFinEquiv finProdFinEquiv
    ((statePower τ n).matrix ⊗ₖ (statePower τ 1).matrix)
  have h := reindexChannel_apply (channelAddEquiv a n 1).symm
    (channelAddEquiv b n 1).symm Φ (statePower τ (n+1)).matrix
  have hi : Matrix.reindex (channelAddEquiv a n 1).symm (channelAddEquiv a n 1).symm
      (statePower τ (n+1)).matrix = X := by
    rw [← statePower_add_matrix τ n 1]
    ext i j; simp [X,Matrix.reindex_apply]
  rw [hi] at h
  change _ = Matrix.reindex _ _ (Φ.toLinearMap (statePower τ (n+1)).matrix) at h
  rw [hΦ.2] at h
  have ho : Matrix.reindex (channelAddEquiv b n 1).symm (channelAddEquiv b n 1).symm
      (statePower ω (n+1)).matrix = Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((statePower ω n).matrix ⊗ₖ (statePower ω 1).matrix) := by
    rw [← statePower_add_matrix ω n 1]
    ext i j; simp [Matrix.reindex_apply]
  rw [ho] at h
  rw [h,discardRight_apply_product,(statePower ω 1).trace_one,one_smul]

/-- Definition 14 holds with precisely the original faithful input state. -/
theorem statePreserving_quantitative (τ : State a) (ω : State b) (hτ : τ.matrix.PosDef) :
    QuantitativeAt (statePreservingFamily τ ω) τ where
  faithful := hτ
  permutation_closed n hn π Φ hΦ := statePreserving_permutation τ ω n π Φ hΦ
  marginal_closed n hn Φ hΦ := statePreserving_marginal τ ω n Φ hΦ


open ChannelEntropy RelativeEntropy OperationalTesting ChannelLocality DivergenceOptimization

/-- Flattening a scalar left tensor factor implements the numerical one-times transport. -/
theorem reindex_one_tensor {d : ℕ} (X : Operator d) :
    Matrix.reindex (finCongr (Nat.one_mul d)) (finCongr (Nat.one_mul d))
      (Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Operator 1) ⊗ₖ X)) = X := by
  ext i j
  simp [Matrix.reindex_apply,finProdFinEquiv,Matrix.one_apply]
  split_ifs with h
  · congr 1 <;> apply Fin.ext <;> simp [Fin.modNat, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]
  · exfalso; apply h; exact Subsingleton.elim _ _

theorem scalar_tensor_reindex {d : ℕ} (ρ : State d) :
    (scalarState.tensor ρ).reindex (finCongr (Nat.one_mul d)) = ρ := by
  apply State.eq_of_matrix_eq
  exact reindex_one_tensor ρ.matrix

/-- An input and effect without an ancillary reference, embedded into the unrestricted model. -/
def unassistedTest (τ : State a) (T : Effect b) : ChannelTest a b where
  reference := 1
  input := scalarState.tensor τ
  effect := reindexEffect (finCongr (Nat.one_mul b)).symm T

theorem unassisted_output (Φ : KrausChannel a b) (τ : State a) :
    outputState Φ 1 (scalarState.tensor τ) = scalarState.tensor (Φ.onState τ) := by
  rw [outputState_eq_tensor]
  apply State.eq_of_matrix_eq
  change ((KrausChannel.identity 1).tensor Φ).apply
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (scalarState.matrix ⊗ₖ τ.matrix)) = _
  rw [KrausChannel.tensor_apply_product,KrausChannel.identity_apply]
  rfl

theorem unassistedTest_acceptance (τ : State a) (T : Effect b) (Φ : KrausChannel a b) :
    (unassistedTest τ T).acceptance Φ = T.probability (Φ.onState τ) := by
  change (reindexEffect (finCongr (Nat.one_mul b)).symm T).probability
    (outputState Φ 1 (scalarState.tensor τ)) = _
  rw [unassisted_output]
  have h := reindexEffect_probability (finCongr (Nat.one_mul b)).symm T (Φ.onState τ)
  have he : (Φ.onState τ).reindex (finCongr (Nat.one_mul b)).symm =
      scalarState.tensor (Φ.onState τ) := by
    apply State.eq_of_matrix_eq
    have hh := congrArg (fun ρ : State b => ρ.reindex (finCongr (Nat.one_mul b)).symm)
      (scalar_tensor_reindex (Φ.onState τ))
    simpa [State.reindex_matrix,Matrix.reindex_apply] using
      (congrArg State.matrix hh).symm
  rw [he] at h
  exact h

theorem umegaki_onState_le_channelD (Φ Ψ : KrausChannel a b) (τ : State a) :
    umegaki (Φ.onState τ) (Ψ.onState τ) ≤ channelD Φ Ψ := by
  have h := umegaki_mixed_reference_le Φ Ψ (scalarState.tensor τ)
  rw [unassisted_output,unassisted_output,umegaki_tensor,umegaki_self,zero_add] at h
  exact h

/-- A state-preserving alternative has the specified output exactly. -/
theorem onState_of_preserving {τ : State a} {ω : State b} {Φ : KrausChannel a b}
    (hΦ : Φ.toLinearMap ∈ preservingSet τ ω) : Φ.onState τ = ω :=
  State.eq_of_matrix_eq hΦ.2

/-- Single-block exact entropy for the full state-preserving alternative set. -/
theorem preserving_replacer_entropy (τ : State a) (ρ ω : State b) (ha : 0<a) :
    familyEntropy (ReplacerChannel.channel a ρ) (preservingSet τ ω) = umegaki ρ ω := by
  apply le_antisymm
  · exact (familyEntropy_le _ (ReplacerChannel.channel a ω) _ (replacer_preserving τ ω)).trans
      (ReplacerChannel.channelD_eq ρ ω ha).le
  · apply le_iInf
    intro M
    have h := umegaki_onState_le_channelD (ReplacerChannel.channel a ρ) M.val τ
    rw [ReplacerChannel.channel_onState,onState_of_preserving M.property] at h
    exact h

/-- The exact finite-block entropy identity in Proposition 19. -/
theorem statePreserving_replacer_entropy (τ : State a) (ρ ω : State b) (ha : 0<a) (n : ℕ) :
    familyEntropy ((ReplacerChannel.channel a ρ).tensorPower n) (statePreservingFamily τ ω n) =
      ((n:ℝ):EReal)*umegaki ρ ω := by
  have he := (ReplacerChannel.tensorPower_map (n:=a) ρ n).trans
    (ReplacerChannel.channel_map (a^n) (statePower ρ n)).symm
  have hcongr : familyEntropy ((ReplacerChannel.channel a ρ).tensorPower n)
      (statePreservingFamily τ ω n) =
      familyEntropy (ReplacerChannel.channel (a^n) (statePower ρ n)) (statePreservingFamily τ ω n) := by
    apply iInf_congr
    intro M
    exact channelD_congr _ _ _ _ he rfl
  rw [hcongr]
  change familyEntropy _ (preservingSet (statePower τ n) (statePower ω n)) = _
  rw [preserving_replacer_entropy _ _ _ (pow_pos ha n),ReplacerChannel.umegaki_statePower]

/-- Literal state hypothesis-testing optimum at a fixed tolerance. -/
def stateBeta (ρ σ : State b) (ε : ℝ) : ENNReal :=
  ⨅ T : {T : Effect b // 1-ε ≤ T.probability ρ}, ENNReal.ofReal (T.val.probability σ)

/-- Prepare a state on the left while leaving the tested system unchanged. -/
def prependState {r : ℕ} (ω : State r) (b : ℕ) : KrausChannel b (r*b) :=
  reindexChannel (finCongr (Nat.one_mul b)) (Equiv.refl _)
    ((ReplacerChannel.channel 1 ω).tensor (KrausChannel.identity b))

theorem prependState_onState {r : ℕ} (ω : State r) (ρ : State b) :
    (prependState ω b).onState ρ = ω.tensor ρ := by
  apply State.eq_of_matrix_eq
  have h := reindexChannel_apply (finCongr (Nat.one_mul b)) (Equiv.refl _)
    ((ReplacerChannel.channel 1 ω).tensor (KrausChannel.identity b))
    (Matrix.reindex finProdFinEquiv finProdFinEquiv ((1:Operator 1) ⊗ₖ ρ.matrix))
  rw [reindex_one_tensor,KrausChannel.tensor_apply_product,
    KrausChannel.identity_apply,ReplacerChannel.channel_apply] at h
  simpa using h

/-- Every arbitrary tester of replacers reduces to one state effect, uniformly in the prepared state. -/
theorem exists_replacer_effect (t : ChannelTest a b) :
    ∃ T : Effect b, ∀ ρ : State b, T.probability ρ = t.acceptance (ReplacerChannel.channel a ρ) := by
  let φ := MixedReferencePurification.purificationInput t.input
  let Tbig := ((MixedReferencePurification.traceFirst (t.reference*a) t.reference).tensor
    (KrausChannel.identity b)).pullbackEffect t.effect
  obtain ⟨Γ,hΓ⟩ := PureReferenceRecovery.exists_output_reference_recovery (m:=b) φ
  let ω := PureReferenceRecovery.inputDensity φ
  let T := (Γ.tensor (KrausChannel.identity b)).pullbackEffect Tbig
  refine ⟨(prependState ω b).pullbackEffect T,?_⟩
  intro ρ
  rw [KrausChannel.pullbackEffect_probability,prependState_onState]
  rw [← ReplacerChannel.canonical_output ρ ω]
  change ((Γ.tensor (KrausChannel.identity b)).pullbackEffect Tbig).probability _ = _
  rw [KrausChannel.pullbackEffect_probability,hΓ]
  change (((MixedReferencePurification.traceFirst (t.reference*a) t.reference).tensor
    (KrausChannel.identity b)).pullbackEffect t.effect).probability
      (pureOutput (ReplacerChannel.channel a ρ) (MixedReferencePurification.purificationInput t.input)) = _
  rw [KrausChannel.pullbackEffect_probability,MixedReferencePurification.outputState_recovered]
  rfl

/-- The uniform composite testing problem is exactly state testing for a replacer target. -/
theorem preserving_replacer_beta (τ : State a) (ρ ω : State b) (ε : ℝ) :
    compositeBeta (ReplacerChannel.channel a ρ) (preservingSet τ ω) ε = stateBeta ρ ω ε := by
  apply le_antisymm
  · apply le_iInf
    intro T
    refine iInf_le_of_le ⟨unassistedTest τ T.val,?_⟩ ?_
    · simpa only [unassistedTest_acceptance,ReplacerChannel.channel_onState] using T.property
    · apply iSup_le
      intro M
      rw [unassistedTest_acceptance,onState_of_preserving M.property]
  · apply le_iInf
    intro t
    obtain ⟨T,hT⟩ := exists_replacer_effect t.val
    refine (iInf_le_of_le ⟨T,by rw [hT]; exact t.property⟩ le_rfl).trans ?_
    rw [hT]
    exact acceptance_le_worst _ t.val (ReplacerChannel.channel a ω) (replacer_preserving τ ω)


/-- Operational acceptance depends on the represented map, not Kraus slots. -/
theorem channelTest_acceptance_congr {Φ Ψ : KrausChannel a b}
    (h : Φ.toLinearMap = Ψ.toLinearMap) (t : ChannelTest a b) :
    t.acceptance Φ = t.acceptance Ψ := by
  have he : outputState Φ t.reference t.input = outputState Ψ t.reference t.input := by
    apply State.eq_of_matrix_eq
    change Matrix.reindex _ _ (Φ.amplify _ _) = Matrix.reindex _ _ (Ψ.amplify _ _)
    rw [← MatrixMap.amplify_toLinearMap,← MatrixMap.amplify_toLinearMap,h]
  exact congrArg t.effect.probability he

theorem compositeBeta_congr_target {Φ Ψ : KrausChannel a b}
    (h : Φ.toLinearMap = Ψ.toLinearMap) (F : Set (MatrixMap a b)) (ε : ℝ) :
    compositeBeta Φ F ε = compositeBeta Ψ F ε := by
  apply le_antisymm
  · apply le_iInf
    intro t
    exact iInf_le_of_le ⟨t.val,by rw [channelTest_acceptance_congr h]; exact t.property⟩ le_rfl
  · apply le_iInf
    intro t
    exact iInf_le_of_le ⟨t.val,by rw [← channelTest_acceptance_congr h]; exact t.property⟩ le_rfl

/-- The exact finite-block testing identity in Proposition 19. -/
theorem statePreserving_replacer_beta (τ : State a) (ρ ω : State b) (n : ℕ) (ε : ℝ) :
    compositeBeta ((ReplacerChannel.channel a ρ).tensorPower n) (statePreservingFamily τ ω n) ε =
      stateBeta (statePower ρ n) (statePower ω n) ε := by
  rw [compositeBeta_congr_target ((ReplacerChannel.tensorPower_map (n:=a) ρ n).trans
    (ReplacerChannel.channel_map (a^n) (statePower ρ n)).symm)]
  exact preserving_replacer_beta _ _ _ _

/-- Proposition 19, all five family conditions and both exact finite-block identities. -/
theorem proposition_19 (τ : State a) (ω ρ : State b) (ha : 0<a)
    (hτ : τ.matrix.PosDef) (hω : ω.matrix.PosDef) :
    Admissible (statePreservingFamily τ ω) ∧
    QuantitativeAt (statePreservingFamily τ ω) τ ∧
    (∀ n, familyEntropy ((ReplacerChannel.channel a ρ).tensorPower n)
      (statePreservingFamily τ ω n) = ((n:ℝ):EReal)*umegaki ρ ω) ∧
    (∀ n ε, compositeBeta ((ReplacerChannel.channel a ρ).tensorPower n)
      (statePreservingFamily τ ω n) ε = stateBeta (statePower ρ n) (statePower ω n) ε) := by
  exact ⟨statePreserving_admissible τ ω hω,statePreserving_quantitative τ ω hτ,
    statePreserving_replacer_entropy τ ρ ω ha,statePreserving_replacer_beta τ ρ ω⟩


/-- The state infimum is an attained minimum for every nonnegative tolerance. -/
theorem stateBeta_attained (ρ σ : State b) (ε : ℝ) (hε : 0≤ε) :
    ∃ T : Effect b, 1-ε ≤ T.probability ρ ∧ stateBeta ρ σ ε = ENNReal.ofReal (T.probability σ) := by
  let S : Set (Operator b) := ParallelTestingAttainment.effectSet b ∩
    {X | 1-ε ≤ (X*ρ.matrix).trace.re}
  have hc (ζ : State b) : Continuous (fun X : Operator b => (X*ζ.matrix).trace.re) := by
    unfold Matrix.trace Matrix.diag
    fun_prop
  have hS : IsCompact S := (ParallelTestingAttainment.isCompact_effectSet b).inter_right
    (isClosed_le continuous_const (hc ρ))
  have hSne : S.Nonempty := by
    refine ⟨1,⟨⟨Matrix.PosSemidef.one,by simpa using (Matrix.PosSemidef.zero (n:=Fin b) (R:=ℂ))⟩,?_⟩⟩
    change 1-ε ≤ ((1:Operator b)*ρ.matrix).trace.re
    simp only [Matrix.one_mul,ρ.trace_one,Complex.one_re]
    linarith
  obtain ⟨X,hX,hmin⟩ := hS.exists_isMinOn hSne (hc σ).continuousOn
  let T : Effect b := ⟨X,hX.1.1,hX.1.2⟩
  refine ⟨T,hX.2,le_antisymm (iInf_le_of_le ⟨T,hX.2⟩ le_rfl) ?_⟩
  apply le_iInf
  intro U
  exact ENNReal.ofReal_le_ofReal (hmin ⟨⟨U.val.positive,U.val.complement_positive⟩,U.property⟩)

end GeneralizedChannelStein
