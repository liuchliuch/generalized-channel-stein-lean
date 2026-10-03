import GeneralizedChannelStein.CovariantFamilies
import GeneralizedChannelStein.ChannelSpace

/-! Literal inverse images of free channels under a fixed physical output channel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelPowerReindex ChannelEntropy TestingSDP PerfectDiscrimination
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b c : ℕ}

def outputPreimageSet (D : KrausChannel c b) (F : Set (MatrixMap a b)) : Set (MatrixMap a c) :=
  {Φ | IsChannel Φ ∧ D.toLinearMap.comp Φ ∈ F}

def postChoi (D : KrausChannel c b) : BipartiteOperator a c →ₗ[ℝ] BipartiteOperator a b where
  toFun C := fun i j => D.toLinearMap (fun x y => C (i.1,x) (j.1,y)) i.2 j.2
  map_add' C E := by
    ext i j
    change D.toLinearMap ((fun x y => C (i.1,x) (j.1,y)) + (fun x y => E (i.1,x) (j.1,y))) i.2 j.2 = _
    rw [map_add]
    rfl
  map_smul' r C := by
    ext i j
    change D.toLinearMap ((r:ℂ) • (fun x y => C (i.1,x) (j.1,y))) i.2 j.2 = _
    rw [map_smul]
    rfl

theorem postChoi_choi (D : KrausChannel c b) (Φ : MatrixMap a c) :
    postChoi D (MatrixMap.choi Φ)=MatrixMap.choi (D.toLinearMap.comp Φ) := by
  ext i j
  rfl

theorem outputPreimageSet_choi (D : KrausChannel c b) (F : Set (MatrixMap a b)) :
    MatrixMap.choi '' outputPreimageSet D F =
      channelChoiSet a c ∩ (postChoi D ⁻¹' (MatrixMap.choi '' F)) := by
  ext C
  constructor
  · rintro ⟨Φ,⟨hΦ,hF⟩,rfl⟩
    refine ⟨?_,⟨_,hF,(postChoi_choi D Φ).symm⟩⟩
    rw [channelChoiSet_eq_image]
    exact ⟨Φ,hΦ,rfl⟩
  · rintro ⟨hC,hF⟩
    rw [channelChoiSet_eq_image] at hC
    obtain ⟨Φ,hΦ,rfl⟩ := hC
    obtain ⟨M,hM,he⟩ := hF
    refine ⟨Φ,⟨hΦ,?_⟩,rfl⟩
    have hm : M=D.toLinearMap.comp Φ := MatrixMap.choi_injective (he.trans (postChoi_choi D Φ))
    rwa [←hm]

theorem outputPreimageSet_compact (D : KrausChannel c b) (F : Set (MatrixMap a b))
    (hF : IsCompact (MatrixMap.choi '' F)) :
    IsCompact (MatrixMap.choi '' outputPreimageSet D F) := by
  rw [outputPreimageSet_choi]
  exact (isCompact_channelChoiSet _ _).inter_right
    (hF.isClosed.preimage (postChoi D).continuous_of_finiteDimensional)

theorem outputPreimageSet_convex (D : KrausChannel c b) (F : Set (MatrixMap a b))
    (hF : Convex ℝ (MatrixMap.choi '' F)) :
    Convex ℝ (MatrixMap.choi '' outputPreimageSet D F) := by
  rw [outputPreimageSet_choi]
  exact (convex_channelChoiSet _ _).inter (hF.linear_preimage (postChoi D))

def outputPreimageFamily (D : KrausChannel c b) (F : AlternativeFamily a b) : AlternativeFamily a c :=
  fun n => outputPreimageSet (D.tensorPower n) (F n)

theorem compose_map (D : KrausChannel c b) (Φ : KrausChannel a c) :
    (D.compose Φ).toLinearMap=D.toLinearMap.comp Φ.toLinearMap := by
  ext X i j
  exact congrFun (congrFun (KrausChannel.compose_apply D Φ X) i) j

theorem tensor_compose_apply {a' b' c' : ℕ}
    (D : KrausChannel c b) (E : KrausChannel c' b')
    (Φ : KrausChannel a c) (Ψ : KrausChannel a' c') (X : Operator (a*a')) :
    (D.tensor E).apply ((Φ.tensor Ψ).apply X)=((D.compose Φ).tensor (E.compose Ψ)).apply X := by
  have h := matrixMap_ext_product
    ((D.tensor E).toLinearMap.comp (Φ.tensor Ψ).toLinearMap)
    (((D.compose Φ).tensor (E.compose Ψ)).toLinearMap) (fun Y Z => by
      change (D.tensor E).apply ((Φ.tensor Ψ).apply _) = ((D.compose Φ).tensor (E.compose Ψ)).apply _
      simp only [KrausChannel.tensor_apply_product,KrausChannel.compose_apply])
  exact congrArg (fun L : MatrixMap (a*a') (b*b') => L X) h

theorem post_tensorBlocks (D : KrausChannel c b) (n m : ℕ)
    (Φ : KrausChannel (a^n) (c^n)) (Ψ : KrausChannel (a^m) (c^m)) :
    (D.tensorPower (n+m)).toLinearMap.comp (tensorBlocks n m Φ Ψ).toLinearMap =
      (tensorBlocks n m ((D.tensorPower n).compose Φ) ((D.tensorPower m).compose Ψ)).toLinearMap := by
  ext X i j
  change (D.tensorPower (n+m)).apply ((tensorBlocks n m Φ Ψ).apply X) i j =
    (tensorBlocks n m ((D.tensorPower n).compose Φ) ((D.tensorPower m).compose Ψ)).apply X i j
  simp only [tensorBlocks,reindexChannel_apply_any,tensorPower_add_apply,tensor_compose_apply]

theorem outputPreimage_tensor (D : KrausChannel c b) (F : AlternativeFamily a b)
    (hF : Admissible F) (n m : ℕ) (hn : 0<n) (hm : 0<m)
    (Φ : KrausChannel (a^n) (c^n)) (Ψ : KrausChannel (a^m) (c^m))
    (hΦ : Φ.toLinearMap∈outputPreimageFamily D F n)
    (hΨ : Ψ.toLinearMap∈outputPreimageFamily D F m) :
    (tensorBlocks n m Φ Ψ).toLinearMap∈outputPreimageFamily D F (n+m) := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  change (D.tensorPower (n+m)).toLinearMap.comp (tensorBlocks n m Φ Ψ).toLinearMap∈F (n+m)
  rw [post_tensorBlocks]
  apply hF.tensor_closed n m hn hm
  · simpa only [compose_map] using hΦ.2
  · simpa only [compose_map] using hΨ.2

theorem post_permuteChannel (D : KrausChannel c b) (n : ℕ) (π : Equiv.Perm (Fin n))
    (Φ : KrausChannel (a^n) (c^n)) :
    (D.tensorPower n).toLinearMap.comp (permuteChannel n π Φ).toLinearMap =
      (permuteChannel n π ((D.tensorPower n).compose Φ)).toLinearMap := by
  ext X i j
  change (D.tensorPower n).apply ((permuteChannel n π Φ).apply X) i j =
    (permuteChannel n π ((D.tensorPower n).compose Φ)).apply X i j
  simp only [permuteChannel,reindexChannel_apply_any,power_permutation_apply,KrausChannel.compose_apply]

theorem discard_tensor_rect {e f : ℕ} (D : KrausChannel c b) (E : KrausChannel e f)
    (X : Operator (c*e)) :
    (discardRight b f).apply ((D.tensor E).apply X)=D.apply ((discardRight c e).apply X) := by
  have h := matrixMap_ext_product
    ((discardRight b f).toLinearMap.comp (D.tensor E).toLinearMap)
    (D.toLinearMap.comp (discardRight c e).toLinearMap) (fun Y Z => by
      change (discardRight b f).apply ((D.tensor E).apply _) = D.apply ((discardRight c e).apply _)
      rw [KrausChannel.tensor_apply_product,discardRight_apply_product,discardRight_apply_product,KrausChannel.trace_apply]
      exact (D.toLinearMap.map_smul Z.trace Y).symm)
  exact congrArg (fun L : MatrixMap (c*e) b => L X) h

theorem post_marginalChannel (D : KrausChannel c b) (n : ℕ) (τ : State a)
    (Φ : KrausChannel (a^(n+1)) (c^(n+1))) :
    (D.tensorPower n).toLinearMap.comp (marginalChannel n τ Φ).toLinearMap =
      (marginalChannel n τ ((D.tensorPower (n+1)).compose Φ)).toLinearMap := by
  ext X i j
  change (D.tensorPower n).apply ((marginalChannel n τ Φ).apply X) i j =
    (marginalChannel n τ ((D.tensorPower (n+1)).compose Φ)).apply X i j
  simp only [marginalChannel,KrausChannel.compose_apply,reindexChannel_apply_any]
  rw [←discard_tensor_rect,power_add_inverse_apply]

/-- Every local physical output postprocessing preserves the literal F4/F5 inverse-image closure. -/
theorem outputPreimage_quantitative (D : KrausChannel c b) (F : AlternativeFamily a b)
    (τ : State a) (hF : QuantitativeAt F τ) : QuantitativeAt (outputPreimageFamily D F) τ := by
  refine ⟨hF.faithful,?_,?_⟩
  · intro n hn π Φ hΦ
    refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
    change (D.tensorPower n).toLinearMap.comp (permuteChannel n π Φ).toLinearMap∈F n
    rw [post_permuteChannel]
    apply hF.permutation_closed n hn π
    simpa only [compose_map] using hΦ.2
  · intro n hn Φ hΦ
    refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
    change (D.tensorPower n).toLinearMap.comp (marginalChannel n τ Φ).toLinearMap∈F n
    rw [post_marginalChannel]
    apply hF.marginal_closed n hn
    simpa only [compose_map] using hΦ.2

theorem post_replacer_power (D : KrausChannel c b) (η : State c) (ω : State b)
    (hD : D.onState η=ω) (n : ℕ) :
    (D.tensorPower n).toLinearMap.comp ((ReplacerChannel.channel a η).tensorPower n).toLinearMap =
      ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap := by
  rw [ReplacerChannel.tensorPower_map,ReplacerChannel.tensorPower_map]
  have h := congrArg State.matrix (tensorPower_onState D η n)
  rw [hD] at h
  ext X i j
  change (D.tensorPower n).toLinearMap (X.trace • (statePower η n).matrix) i j =
    (X.trace • (statePower ω n).matrix) i j
  rw [map_smul]
  change (X.trace • (D.tensorPower n).apply (statePower η n).matrix) i j = _
  change (D.tensorPower n).apply (statePower η n).matrix = (statePower ω n).matrix at h
  rw [h]

/-- The inverse image is admissible whenever an actual faithful free replacer lifts. -/
theorem outputPreimage_admissible (D : KrausChannel c b) (F : AlternativeFamily a b)
    (hF : Admissible F) (η : State c) (hη : η.matrix.PosDef) (ω : State b)
    (hD : D.onState η=ω)
    (hω : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1) :
    Admissible (outputPreimageFamily D F) := by
  have hmem : ∀ n,0<n → ((ReplacerChannel.channel a η).tensorPower n).toLinearMap∈outputPreimageFamily D F n := by
    intro n hn
    refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
    change (D.tensorPower n).toLinearMap.comp ((ReplacerChannel.channel a η).tensorPower n).toLinearMap∈F n
    rw [post_replacer_power D η ω hD]
    exact replacer_power_mem F hF.tensor_closed ω hω n hn
  refine ⟨?_,?_,?_,?_,?_,⟨η,hη,hmem 1 (by decide)⟩⟩
  · intro n hn Φ hΦ
    exact hΦ.1
  · intro n hn
    exact ⟨_,hmem n hn⟩
  · intro n hn
    exact outputPreimageSet_compact _ _ (hF.compact n hn)
  · intro n hn
    exact outputPreimageSet_convex _ _ (hF.convex n hn)
  · exact outputPreimage_tensor D F hF

end GeneralizedChannelStein
