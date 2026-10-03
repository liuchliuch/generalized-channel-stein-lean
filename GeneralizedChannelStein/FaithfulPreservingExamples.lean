import GeneralizedChannelStein.StatePreserving
import GeneralizedChannelStein.SeparableStates
import GeneralizedChannelStein.EntropyLimit
import GeneralizedChannelStein.CoherentMarginal

/-! Concrete Gibbs, unital-reset, and fixed-marginal examples after Proposition 19. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.FaithfulPreservingExamples
open QuantumChannelStein Matrix ChannelEntropy RelativeEntropy PerfectDiscrimination
  FaithfulDensity ChannelPowerReindex
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
variable {d : ℕ}

/-- The literal finite Gibbs weight, defined by spectral functional calculus. -/
def gibbsWeight (H : Operator d) (hH : H.IsHermitian) (β : ℝ) : Operator d :=
  hH.cfc (fun x => Real.exp (-β*x))

theorem gibbsWeight_posDef (H : Operator d) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsWeight H hH β).PosDef := by
  rw [gibbsWeight,Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply]
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr
  apply Matrix.PosDef.diagonal
  intro i
  change (0:ℂ)<Complex.ofReal (Real.exp (-β*hH.eigenvalues i))
  exact_mod_cast Real.exp_pos (-β*hH.eigenvalues i)

theorem gibbsWeight_trace_pos (hd : 0<d) (H : Operator d) (hH : H.IsHermitian) (β : ℝ) :
    0<(gibbsWeight H hH β).trace.re := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  exact (Complex.pos_iff.mp (gibbsWeight_posDef H hH β).trace_pos).1

/-- The normalized finite-temperature Gibbs state; every real finite β is admitted. -/
def gibbsState (hd : 0<d) (H : Operator d) (hH : H.IsHermitian) (β : ℝ) : State d :=
  normalizePositive hd (gibbsWeight H hH β) (gibbsWeight_posDef H hH β).posSemidef

theorem gibbsState_matrix (hd : 0<d) (H : Operator d) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsState hd H hH β).matrix=(gibbsWeight H hH β).trace.re⁻¹•gibbsWeight H hH β := by
  simp only [gibbsState,normalizePositive,dif_pos (gibbsWeight_trace_pos hd H hH β)]

theorem gibbsState_faithful (hd : 0<d) (H : Operator d) (hH : H.IsHermitian) (β : ℝ) :
    (gibbsState hd H hH β).matrix.PosDef := by
  rw [gibbsState_matrix]
  exact (gibbsWeight_posDef H hH β).smul (inv_pos.mpr (gibbsWeight_trace_pos hd H hH β))

/-- All block CPTP maps that preserve the identity, with no product restriction. -/
def unitalFamily (d : ℕ) : AlternativeFamily d d := fun _n => {Φ | IsChannel Φ ∧ Φ 1=1}

theorem tensorPower_scalar_one (s : ℝ) (d n : ℕ) :
    TensorPower.tensorPower (s•(1:Operator d)) n = s^n•(1:Matrix (TensorPower.Index (Fin d) n) (TensorPower.Index (Fin d) n) ℂ) := by
  induction n with
  | zero =>
    ext i j
    simp [TensorPower.tensorPower,Subsingleton.elim i j]
  | succ n ih =>
    rw [TensorPower.tensorPower_succ,ih,Matrix.smul_kronecker,Matrix.kronecker_smul,
      smul_smul,Matrix.one_kronecker_one,pow_succ']

theorem maximallyMixed_power_matrix (hd : 0<d) (n : ℕ) :
    (statePower (maximallyMixed d hd) n).matrix=((d:ℝ)⁻¹)^n•(1:Operator (d^n)) := by
  change Matrix.reindex (channelIndexEquiv d n) (channelIndexEquiv d n)
    (TensorPower.tensorPower ((d:ℝ)⁻¹•(1:Operator d)) n)=_
  rw [tensorPower_scalar_one]
  ext i j
  simp [Matrix.reindex_apply,Matrix.one_apply]

theorem maximallyMixed_preserving_eq_unital (hd : 0<d) :
    statePreservingFamily (maximallyMixed d hd) (maximallyMixed d hd)=unitalFamily d := by
  funext n
  ext Φ
  change (IsChannel Φ ∧ Φ (statePower (maximallyMixed d hd) n).matrix=(statePower (maximallyMixed d hd) n).matrix) ↔ _
  rw [maximallyMixed_power_matrix]
  have hs : ((d:ℝ)⁻¹)^n≠0 := ne_of_gt (pow_pos (inv_pos.mpr (Nat.cast_pos.mpr hd)) n)
  have hmap : Φ (((d:ℝ)⁻¹)^n•(1:Operator (d^n)))=((d:ℝ)⁻¹)^n•Φ 1 := by
    exact LinearMap.map_smul_of_tower Φ _ _
  rw [hmap]
  constructor
  · rintro ⟨hΦ,h⟩
    exact ⟨hΦ,(smul_right_injective _ hs) h⟩
  · rintro ⟨hΦ,h⟩
    exact ⟨hΦ,by rw [h]⟩


/-- An arbitrary normalized pure state, retaining its actual matrix. -/
def pureState (ψ : Ket (Fin d)) : State d := PhyslibStateBridge.fromMState (MState.pure ψ)

theorem pureState_entropy (ψ : Ket (Fin d)) : EntropyContinuity.entropy (pureState ψ)=0 := by
  rw [EntropyContinuity.entropy_eq_physlib]
  simp [pureState]

theorem supportIncluded_faithful (ρ σ : State d) (hσ : σ.matrix.PosDef) : supportIncluded ρ σ := by
  intro x hx
  have hi := Matrix.mulVec_injective_of_isUnit hσ.isUnit
  have hz : x=0 := hi (by simpa only [Matrix.mulVec_zero] using hx)
  rw [hz]
  exact (LinearMap.ker ρ.matrix.mulVecLin).zero_mem

theorem maximallyMixed_log (hd : 0<d) :
    spectralLog2 (maximallyMixed d hd)=(-Real.logb 2 d)•(1:Operator d) := by
  rw [spectralLog2_eq_cfc]
  change cfc (Real.logb 2) ((d:ℝ)⁻¹•(1:Operator d))=_
  rw [← Algebra.algebraMap_eq_smul_one,cfc_algebraMap,Algebra.algebraMap_eq_smul_one,Real.logb_inv]

theorem pure_relative_maximallyMixed (hd : 0<d) (ψ : Ket (Fin d)) :
    umegaki (pureState ψ) (maximallyMixed d hd)=(Real.logb 2 d:ℝ) := by
  rw [umegaki_of_supportIncluded _ _ (supportIncluded_faithful _ _ (maximallyMixed_posDef d hd))]
  congr 1
  rw [EntropyContinuity.traceFormula_entropy,pureState_entropy,maximallyMixed_log]
  simp [Matrix.trace_smul,(pureState ψ).trace_one,Complex.real_smul]

/-- The pure reset rate against the full unital family is exactly log₂ d. -/
theorem pure_reset_rate (hd : 0<d) (ψ : Ket (Fin d)) :
    steinRate (ReplacerChannel.channel d (pureState ψ)) (unitalFamily d)=Real.logb 2 d := by
  rw [← maximallyMixed_preserving_eq_unital hd]
  let ω := maximallyMixed d hd
  let N := ReplacerChannel.channel d (pureState ψ)
  let F := statePreservingFamily ω ω
  have hF : Admissible F := statePreserving_admissible ω ω (maximallyMixed_posDef d hd)
  have ht := entropy_limit N hd hd F hF
  have hc : Filter.Tendsto (entropyRateReal N F) Filter.atTop (𝓝 (Real.logb 2 d)) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop (0:ℕ)] with n hn
    change Real.logb 2 d=(familyEntropy (N.tensorPower n) (F n)).toReal/(n:ℝ)
    rw [statePreserving_replacer_entropy ω (pureState ψ) ω hd n,pure_relative_maximallyMixed hd ψ]
    rw [← EReal.coe_mul,EReal.toReal_coe]
    field_simp
  exact tendsto_nhds_unique ht hc


def pairSwapEquiv (d : ℕ) : Fin (d*d)≃Fin (d*d) :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

/-- The actual two-register SWAP channel. -/
def pairSwap (d : ℕ) : KrausChannel (d*d) (d*d) := KrausChannel.coordinateChange (pairSwapEquiv d)

theorem pairSwap_apply_product (X Y : Operator d) :
    (pairSwap d).apply (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y)) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Y ⊗ₖ X) := by
  rw [pairSwap,KrausChannel.coordinateChange_apply]
  ext i j
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  simp [pairSwapEquiv,Matrix.reindex_apply,Matrix.kroneckerMap_apply,mul_comm]

theorem pairSwap_marginal (η : State d) :
    (BulkMarginal.pairMarginal η (pairSwap d)).toLinearMap=(ReplacerChannel.channel d η).toLinearMap := by
  apply LinearMap.ext
  intro X
  change (BulkMarginal.pairMarginal η (pairSwap d)).apply X=(ReplacerChannel.channel d η).apply X
  rw [BulkMarginal.pairMarginal,KrausChannel.compose_apply,KrausChannel.compose_apply,
    appendState_apply,pairSwap_apply_product,discardRight_apply_product,ReplacerChannel.channel_apply]

def twoSiteSwap (d : ℕ) : KrausChannel (d^2) (d^2) :=
  reindexChannel (channelAddEquiv d 1 1) (channelAddEquiv d 1 1) (pairSwap (d^1))

theorem twoSiteSwap_preserves (τ : State d) :
    (twoSiteSwap d).toLinearMap∈statePreservingFamily τ τ 2 := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  change (twoSiteSwap d).apply (statePower τ (1+1)).matrix=(statePower τ (1+1)).matrix
  rw [← statePower_add_matrix τ 1 1]
  unfold twoSiteSwap
  rw [reindexChannel_apply,pairSwap_apply_product]

theorem twoSiteSwap_marginal (η : State d) :
    (marginalChannel 1 η (twoSiteSwap d)).toLinearMap=
      (ReplacerChannel.channel (d^1) (statePower η 1)).toLinearMap := by
  let e := channelAddEquiv d 1 1
  let Q := reindexChannel e.symm e.symm (twoSiteSwap d)
  have hQ : Q.toLinearMap=(pairSwap (d^1)).toLinearMap := by
    rw [ChannelTransport.reindexChannel_map]
    change ChannelTransport.reindexMap e.symm e.symm
      (reindexChannel e e (pairSwap (d^1))).toLinearMap=_
    rw [ChannelTransport.reindexChannel_map,ChannelTransport.reindexMap_inverse]
  have hm : (marginalChannel 1 η (twoSiteSwap d)).toLinearMap=
      (BulkMarginal.pairMarginal (statePower η 1) (pairSwap (d^1))).toLinearMap := by
    apply LinearMap.ext
    intro X
    change (BulkMarginal.pairMarginal (statePower η 1) Q).apply X=
      (BulkMarginal.pairMarginal (statePower η 1) (pairSwap (d^1))).apply X
    simp only [BulkMarginal.pairMarginal,KrausChannel.compose_apply]
    have h := congrArg (fun Φ : MatrixMap (d^1*d^1) (d^1*d^1) => Φ ((appendState (d^1) (statePower η 1)).apply X)) hQ
    exact congrArg (discardRight (d^1) (d^1)).apply h
  exact hm.trans (pairSwap_marginal (statePower η 1))

/-- The arbitrary inserted state is the entire remaining output state. -/
theorem pairSwap_marginal_preserves_iff (τ η : State d) :
    (BulkMarginal.pairMarginal η (pairSwap d)).toLinearMap∈preservingSet τ τ ↔ η=τ := by
  rw [pairSwap_marginal]
  constructor
  · intro h
    apply State.eq_of_matrix_eq
    have he := h.2
    change (ReplacerChannel.channel d η).apply τ.matrix=τ.matrix at he
    simpa only [ReplacerChannel.channel_apply,τ.trace_one,one_smul] using he
  · intro h
    subst η
    exact replacer_preserving τ τ

/-- Maximally mixed insertion is not allowed by the fixed-state condition when
that state differs from the family's specified faithful witness. -/
theorem maximallyMixed_insertion_fails (hd : 0<d) (τ : State d) (hτ : τ≠maximallyMixed d hd) :
    (BulkMarginal.pairMarginal (maximallyMixed d hd) (pairSwap d)).toLinearMap∉preservingSet τ τ := by
  rw [pairSwap_marginal_preserves_iff]
  exact Ne.symm hτ


theorem one_power_reindex (ρ : State d) : (statePower ρ 1).reindex (finCongr (Nat.pow_one d))=ρ := by
  rw [StatePowerRenyi.statePower_succ ρ 0]
  have hz : statePower ρ 0=scalarState := ParallelBlockTests.state_one_unique _ _
  rw [hz]
  apply State.eq_of_matrix_eq
  simpa only [State.reindex_matrix,State.tensor_matrix,scalarState,Matrix.reindex_apply,
    Matrix.submatrix_submatrix] using reindex_tensor_one ρ.matrix

theorem twoSiteSwap_marginal_preserves_iff (τ η : State d) :
    (marginalChannel 1 η (twoSiteSwap d)).toLinearMap∈statePreservingFamily τ τ 1 ↔ η=τ := by
  rw [twoSiteSwap_marginal]
  constructor
  · intro h
    have he := h.2
    change (ReplacerChannel.channel (d^1) (statePower η 1)).apply (statePower τ 1).matrix=(statePower τ 1).matrix at he
    rw [ReplacerChannel.channel_apply,(statePower τ 1).trace_one,one_smul] at he
    have hs := State.eq_of_matrix_eq he
    have hc := congrArg (fun ρ : State (d^1) => ρ.reindex (finCongr (Nat.pow_one d))) hs
    simpa only [one_power_reindex] using hc
  · intro h
    subst η
    exact replacer_preserving (statePower τ 1) (statePower τ 1)

theorem gibbsPreserving_all_axioms {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (HA : Operator a) (hA : HA.IsHermitian) (HB : Operator b) (hB : HB.IsHermitian) (βA βB : ℝ) :
    Admissible (statePreservingFamily (gibbsState ha HA hA βA) (gibbsState hb HB hB βB)) ∧
      QuantitativeAt (statePreservingFamily (gibbsState ha HA hA βA) (gibbsState hb HB hB βB)) (gibbsState ha HA hA βA) :=
  ⟨statePreserving_admissible _ _ (gibbsState_faithful hb HB hB βB),
    statePreserving_quantitative _ _ (gibbsState_faithful ha HA hA βA)⟩

end GeneralizedChannelStein.FaithfulPreservingExamples
