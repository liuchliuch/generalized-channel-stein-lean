import GeneralizedChannelStein.CovariantFamilies
import QuantumChannelStein.FaithfulDensity

/-! Full MIO and DIO block families. The constraints act on arbitrary matrices,
so correlated channels are included and no product-channel restriction is imposed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelPowerReindex PerfectDiscrimination Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- The image of an input projection is sent into the fixed points of an output projection.
The definition makes sense for all local channels; dephasing gives exactly MIO. -/
def imagePreservingFamily (A : KrausChannel a a) (B : KrausChannel b b) : AlternativeFamily a b :=
  fun n => {Φ | IsChannel Φ ∧ ∀ X,
    (B.tensorPower n).apply (Φ ((A.tensorPower n).apply X)) = Φ ((A.tensorPower n).apply X)}

def imageChoiConstraint (A : KrausChannel a a) (B : KrausChannel b b) (n : ℕ)
    (C : TestingSDP.BipartiteOperator (a^n) (b^n)) : Prop := ∀ X,
  (B.tensorPower n).apply (choiAction C ((A.tensorPower n).apply X)) =
    choiAction C ((A.tensorPower n).apply X)

theorem imagePreserving_choi_image (A : KrausChannel a a) (B : KrausChannel b b) (n : ℕ) :
    MatrixMap.choi '' imagePreservingFamily A B n = channelChoiSet (a^n) (b^n) ∩
      {C | imageChoiConstraint A B n C} := by
  apply channelSlice_choi_image
  intro Φ
  simp only [imageChoiConstraint,choiAction_choi]

theorem isClosed_imageChoiConstraint (A : KrausChannel a a) (B : KrausChannel b b) (n : ℕ) :
    IsClosed {C | imageChoiConstraint A B n C} := by
  have he : {C | imageChoiConstraint A B n C} = ⋂ X,
      {C | (B.tensorPower n).apply (choiAction C ((A.tensorPower n).apply X)) =
        choiAction C ((A.tensorPower n).apply X)} := by ext C; simp [imageChoiConstraint]
  rw [he]
  apply isClosed_iInter; intro X
  exact isClosed_eq ((B.tensorPower n).toLinearMap.continuous_of_finiteDimensional.comp
    (continuous_choiAction _)) (continuous_choiAction _)

theorem convex_imageChoiConstraint (A : KrausChannel a a) (B : KrausChannel b b) (n : ℕ) :
    Convex ℝ {C | imageChoiConstraint A B n C} := by
  intro C hC D hD r s hr hs hrs X
  rw [choiAction_mix]
  change (B.tensorPower n).toLinearMap (r • choiAction C _+s • choiAction D _) = _
  rw [map_add,LinearMap.map_smul_of_tower,LinearMap.map_smul_of_tower]
  change r • (B.tensorPower n).apply _+s • (B.tensorPower n).apply _ = _
  rw [hC,hD]

/-- A replacer with invariant output satisfies the image constraint at all blocklengths. -/
theorem replacer_mem_imagePreserving (A : KrausChannel a a) (B : KrausChannel b b)
    (ω : State b) (hω : B.onState ω=ω) (n : ℕ) :
    ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ imagePreservingFamily A B n := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  intro X
  rw [ReplacerChannel.tensorPower_map]
  change (B.tensorPower n).toLinearMap
    (((A.tensorPower n).apply X).trace • (statePower ω n).matrix) = _
  rw [map_smul]
  have h := congrArg State.matrix (tensorPower_onState B ω n)
  rw [hω] at h
  change (B.tensorPower n).toLinearMap (statePower ω n).matrix = (statePower ω n).matrix at h
  rw [h]
  rfl

theorem tensor_image_constraint {c d : ℕ} (Φ : KrausChannel a b) (Ψ : KrausChannel c d)
    (A : KrausChannel a a) (B : KrausChannel b b) (C : KrausChannel c c) (D : KrausChannel d d)
    (hΦ : ∀ X, B.apply (Φ.apply (A.apply X))=Φ.apply (A.apply X))
    (hΨ : ∀ X, D.apply (Ψ.apply (C.apply X))=Ψ.apply (C.apply X)) :
    ∀ X, (B.tensor D).apply ((Φ.tensor Ψ).apply ((A.tensor C).apply X)) =
      (Φ.tensor Ψ).apply ((A.tensor C).apply X) := by
  have h := matrixMap_ext_product
    ((B.tensor D).toLinearMap.comp ((Φ.tensor Ψ).toLinearMap.comp (A.tensor C).toLinearMap))
    ((Φ.tensor Ψ).toLinearMap.comp (A.tensor C).toLinearMap) (fun X Y => by
      change (B.tensor D).apply ((Φ.tensor Ψ).apply ((A.tensor C).apply _)) =
        (Φ.tensor Ψ).apply ((A.tensor C).apply _)
      simp only [KrausChannel.tensor_apply_product,hΦ,hΨ])
  intro X
  exact congrArg (fun f : MatrixMap (a*c) (b*d) => f X) h

theorem imagePreserving_tensor (A : KrausChannel a a) (B : KrausChannel b b) (n m : ℕ)
    (Φ : KrausChannel (a^n) (b^n)) (Ψ : KrausChannel (a^m) (b^m))
    (hΦ : Φ.toLinearMap ∈ imagePreservingFamily A B n)
    (hΨ : Ψ.toLinearMap ∈ imagePreservingFamily A B m) :
    (tensorBlocks n m Φ Ψ).toLinearMap ∈ imagePreservingFamily A B (n+m) := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  intro X
  change (B.tensorPower (n+m)).apply ((tensorBlocks n m Φ Ψ).apply _) =
    (tensorBlocks n m Φ Ψ).apply _
  simp only [tensorBlocks,reindexChannel_apply_any,power_add_inverse_apply,tensorPower_add_apply]
  rw [tensor_image_constraint Φ Ψ _ _ _ _ (hΦ.2) (hΨ.2)]

theorem imagePreserving_permutation (A : KrausChannel a a) (B : KrausChannel b b) (n : ℕ)
    (π : Equiv.Perm (Fin n)) (Φ : KrausChannel (a^n) (b^n))
    (hΦ : Φ.toLinearMap ∈ imagePreservingFamily A B n) :
    (permuteChannel n π Φ).toLinearMap ∈ imagePreservingFamily A B n := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  intro X
  obtain ⟨X,rfl⟩ := (Matrix.reindexLinearEquiv ℂ ℂ (sitePermutation a n π) (sitePermutation a n π)).surjective X
  change (B.tensorPower n).apply ((permuteChannel n π Φ).apply
    ((A.tensorPower n).apply (Matrix.reindex _ _ X))) =
    (permuteChannel n π Φ).apply ((A.tensorPower n).apply (Matrix.reindex _ _ X))
  rw [power_permutation_apply]
  simp only [permuteChannel,reindexChannel_apply,power_permutation_apply]
  change Matrix.reindex _ _ ((B.tensorPower n).apply (Φ.toLinearMap _)) = Matrix.reindex _ _ (Φ.toLinearMap _)
  rw [hΦ.2]

theorem imagePreserving_marginal (A : KrausChannel a a) (B : KrausChannel b b)
    (τ : State a) (hτ : A.onState τ=τ) (n : ℕ)
    (Φ : KrausChannel (a^(n+1)) (b^(n+1)))
    (hΦ : Φ.toLinearMap ∈ imagePreservingFamily A B (n+1)) :
    (marginalChannel n τ Φ).toLinearMap ∈ imagePreservingFamily A B n := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  intro X
  let Ψ := reindexChannel (channelAddEquiv a n 1).symm (channelAddEquiv b n 1).symm Φ
  have hΨ (Y : Operator (a^n*a^1)) :
      ((B.tensorPower n).tensor (B.tensorPower 1)).apply
        (Ψ.apply (((A.tensorPower n).tensor (A.tensorPower 1)).apply Y)) =
      Ψ.apply (((A.tensorPower n).tensor (A.tensorPower 1)).apply Y) := by
    simp only [Ψ,reindexChannel_apply_any,Equiv.symm_symm]
    rw [← tensorPower_add_apply]
    rw [← power_add_inverse_apply]
    change Matrix.reindex _ _ ((B.tensorPower (n+1)).apply (Φ.toLinearMap _)) = Matrix.reindex _ _ (Φ.toLinearMap _)
    rw [hΦ.2]
  have hτ1 : (A.tensorPower 1).onState (statePower τ 1)=statePower τ 1 := by
    rw [tensorPower_onState,hτ]
  change (B.tensorPower n).apply ((marginalChannel n τ Φ).apply ((A.tensorPower n).apply X)) =
    (marginalChannel n τ Φ).apply ((A.tensorPower n).apply X)
  simp only [marginalChannel,KrausChannel.compose_apply]
  change (B.tensorPower n).apply ((discardRight _ _).apply (Ψ.apply
    ((appendState (a^n) (statePower τ 1)).apply ((A.tensorPower n).apply X)))) = _
  rw [← append_intertwines _ _ _ hτ1,← discard_tensor_apply _ (B.tensorPower 1),hΨ]

/-- The generic image-preserving class satisfies F1–F3. -/
theorem imagePreserving_admissible (A : KrausChannel a a) (B : KrausChannel b b)
    (ω : State b) (hω : ω.matrix.PosDef) (hωinv : B.onState ω=ω) :
    Admissible (imagePreservingFamily A B) where
  channels n hn Φ hΦ := hΦ.1
  nonempty n hn := ⟨_,replacer_mem_imagePreserving A B ω hωinv n⟩
  compact n hn := by
    rw [imagePreserving_choi_image]
    exact (isCompact_channelChoiSet _ _).inter_right (isClosed_imageChoiConstraint A B n)
  convex n hn := by
    rw [imagePreserving_choi_image]
    exact (convex_channelChoiSet _ _).inter (convex_imageChoiConstraint A B n)
  tensor_closed n m hn hm Φ Ψ hΦ hΨ := imagePreserving_tensor A B n m Φ Ψ hΦ hΨ
  faithful_replacer := ⟨ω,hω,replacer_mem_imagePreserving A B ω hωinv 1⟩

theorem imagePreserving_quantitative (A : KrausChannel a a) (B : KrausChannel b b)
    (τ : State a) (hτ : τ.matrix.PosDef) (hτinv : A.onState τ=τ) :
    QuantitativeAt (imagePreservingFamily A B) τ where
  faithful := hτ
  permutation_closed n hn π Φ hΦ := imagePreserving_permutation A B n π Φ hΦ
  marginal_closed n hn Φ hΦ := imagePreserving_marginal A B τ hτinv n Φ hΦ

/-- Maximally incoherent operations: Delta_B^n M Delta_A^n = M Delta_A^n. -/
def MIOFamily (a b : ℕ) : AlternativeFamily a b :=
  imagePreservingFamily (SharpDivergence.diagonalChannel a) (SharpDivergence.diagonalChannel b)

/-- Dephasing covariant operations: M Delta_A^n = Delta_B^n M. -/
def DIOFamily (a b : ℕ) : AlternativeFamily a b :=
  covariantFamily (G:=Unit) (fun _ => SharpDivergence.diagonalChannel a)
    (fun _ => SharpDivergence.diagonalChannel b)

theorem diagonalChannel_maximallyMixed (d : ℕ) (hd : 0<d) :
    (SharpDivergence.diagonalChannel d).onState (FaithfulDensity.maximallyMixed d hd) =
      FaithfulDensity.maximallyMixed d hd := by
  apply State.eq_of_matrix_eq
  change (SharpDivergence.diagonalChannel d).apply _ = _
  rw [SharpDivergence.diagonalChannel_apply]
  ext i j
  simp [FaithfulDensity.maximallyMixed,Matrix.diagonal,Matrix.diag,Matrix.one_apply]

/-- Proposition 20, including the exact faithful maximally-mixed witnesses for both classes. -/
theorem proposition_20 (ha : 0<a) (hb : 0<b) :
    Admissible (MIOFamily a b) ∧
    QuantitativeAt (MIOFamily a b) (FaithfulDensity.maximallyMixed a ha) ∧
    Admissible (DIOFamily a b) ∧
    QuantitativeAt (DIOFamily a b) (FaithfulDensity.maximallyMixed a ha) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact imagePreserving_admissible _ _ _ (FaithfulDensity.maximallyMixed_posDef b hb)
      (diagonalChannel_maximallyMixed b hb)
  · exact imagePreserving_quantitative _ _ _ (FaithfulDensity.maximallyMixed_posDef a ha)
      (diagonalChannel_maximallyMixed a ha)
  · exact covariant_admissible _ _ _ (FaithfulDensity.maximallyMixed_posDef b hb)
      (fun _ => diagonalChannel_maximallyMixed b hb)
  · exact covariant_quantitative _ _ _ (FaithfulDensity.maximallyMixed_posDef a ha)
      (fun _ => diagonalChannel_maximallyMixed a ha)

end GeneralizedChannelStein
