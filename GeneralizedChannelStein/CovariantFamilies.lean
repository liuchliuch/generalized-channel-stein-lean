import GeneralizedChannelStein.StatePreserving
import QuantumChannelStein.SharpUnitary
import QuantumChannelStein.ParallelBlockTests

/-! Full block-channel covariance and arbitrary intersections with common witnesses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelPowerReindex PerfectDiscrimination Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {a b : ℕ}

/-- Intersections take place in the ambient CPTP space, including for an empty index type. -/
def familyIntersection {ι : Type*} (F : ι → AlternativeFamily a b) : AlternativeFamily a b :=
  fun n => {Φ | IsChannel Φ ∧ ∀ i, Φ ∈ F i n}

theorem familyIntersection_choi {ι : Type*} (F : ι → AlternativeFamily a b) (n : ℕ) :
    MatrixMap.choi '' familyIntersection F n =
      channelChoiSet (a^n) (b^n) ∩ ⋂ i, MatrixMap.choi '' F i n := by
  ext C
  constructor
  · rintro ⟨Φ,hΦ,rfl⟩
    refine ⟨?_,Set.mem_iInter.mpr fun i => ⟨Φ,hΦ.2 i,rfl⟩⟩
    rw [channelChoiSet_eq_image]; exact ⟨Φ,hΦ.1,rfl⟩
  · rintro ⟨hC,hF⟩
    rw [channelChoiSet_eq_image] at hC
    obtain ⟨Φ,hΦ,rfl⟩ := hC
    refine ⟨Φ,⟨hΦ,?_⟩,rfl⟩
    intro i
    obtain ⟨Ψ,hΨ,heq⟩ := Set.mem_iInter.mp hF i
    have he := MatrixMap.choi_injective heq
    simpa only [he] using hΨ

/-- Arbitrary intersections preserve the basic axioms when one faithful replacer is shared. -/
theorem intersection_admissible {ι : Type*} (F : ι → AlternativeFamily a b)
    (hF : ∀ i, Admissible (F i)) (ω : State b) (hω : ω.matrix.PosDef)
    (hR : ∀ i, ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F i 1) :
    Admissible (familyIntersection F) where
  channels n hn Φ hΦ := hΦ.1
  nonempty n hn := by
    refine ⟨((ReplacerChannel.channel a ω).tensorPower n).toLinearMap,
      ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩⟩
    intro i
    exact replacer_power_mem (F i) (hF i).tensor_closed ω (hR i) n hn
  compact n hn := by
    rw [familyIntersection_choi]
    exact (isCompact_channelChoiSet _ _).inter_right
      (isClosed_iInter fun i => ((hF i).compact n hn).isClosed)
  convex n hn := by
    rw [familyIntersection_choi]
    exact (convex_channelChoiSet _ _).inter (convex_iInter fun i => (hF i).convex n hn)
  tensor_closed n m hn hm Φ Ψ hΦ hΨ := by
    refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
    intro i
    exact (hF i).tensor_closed n m hn hm Φ Ψ (hΦ.2 i) (hΨ.2 i)
  faithful_replacer := ⟨ω,hω,⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,hR⟩⟩

/-- The same fixed faithful input witness survives intersections. -/
theorem intersection_quantitative {ι : Type*} (F : ι → AlternativeFamily a b)
    (τ : State a) (hτ : τ.matrix.PosDef) (hF : ∀ i, QuantitativeAt (F i) τ) :
    QuantitativeAt (familyIntersection F) τ where
  faithful := hτ
  permutation_closed n hn π Φ hΦ := by
    refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
    intro i
    exact (hF i).permutation_closed n hn π Φ (hΦ.2 i)
  marginal_closed n hn Φ hΦ := by
    refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
    intro i
    exact (hF i).marginal_closed n hn Φ (hΦ.2 i)

/-- General Choi-coordinate description of an extensional channel constraint. -/
theorem channelSlice_choi_image (P : MatrixMap a b → Prop)
    (Q : TestingSDP.BipartiteOperator a b → Prop)
    (hPQ : ∀ Φ, P Φ ↔ Q (MatrixMap.choi Φ)) :
    MatrixMap.choi '' {Φ | IsChannel Φ ∧ P Φ} = channelChoiSet a b ∩ {C | Q C} := by
  ext C
  constructor
  · rintro ⟨Φ,hΦ,rfl⟩
    refine ⟨?_,(hPQ Φ).mp hΦ.2⟩
    rw [channelChoiSet_eq_image]; exact ⟨Φ,hΦ.1,rfl⟩
  · rintro ⟨hC,hQ⟩
    rw [channelChoiSet_eq_image] at hC
    obtain ⟨Φ,hΦ,rfl⟩ := hC
    exact ⟨Φ,⟨hΦ,(hPQ Φ).mpr hQ⟩,rfl⟩

/-- Product inputs span the full bipartite matrix algebra. -/
theorem matrixMap_ext_product {c d u : ℕ} (Φ Ψ : MatrixMap (c*d) u)
    (h : ∀ X : Operator c, ∀ Y : Operator d,
      Φ (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y)) =
      Ψ (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y))) : Φ=Ψ := by
  apply MatrixMap.choi_injective
  ext ⟨i,x⟩ ⟨j,y⟩
  obtain ⟨⟨i₁,i₂⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁,j₂⟩,rfl⟩ := finProdFinEquiv.surjective j
  change Φ (Matrix.single _ _ 1) x y = Ψ (Matrix.single _ _ 1) x y
  rw [← MatrixMap.reindex_product_single]
  exact congrFun (congrFun (h _ _) x) y

/-- Tensoring two commuting squares preserves the square on entangled inputs as well. -/
theorem tensor_intertwines {c d : ℕ} (Φ : KrausChannel a b) (Ψ : KrausChannel c d)
    (A : KrausChannel a a) (B : KrausChannel b b) (C : KrausChannel c c) (D : KrausChannel d d)
    (hΦ : ∀ X, Φ.apply (A.apply X) = B.apply (Φ.apply X))
    (hΨ : ∀ X, Ψ.apply (C.apply X) = D.apply (Ψ.apply X)) :
    ∀ X, (Φ.tensor Ψ).apply ((A.tensor C).apply X) =
      (B.tensor D).apply ((Φ.tensor Ψ).apply X) := by
  have h := matrixMap_ext_product
    ((Φ.tensor Ψ).toLinearMap.comp (A.tensor C).toLinearMap)
    ((B.tensor D).toLinearMap.comp (Φ.tensor Ψ).toLinearMap) (fun X Y => by
      change (Φ.tensor Ψ).apply ((A.tensor C).apply _) =
        (B.tensor D).apply ((Φ.tensor Ψ).apply _)
      simp only [KrausChannel.tensor_apply_product,hΦ,hΨ])
  intro X
  exact congrArg (fun f : MatrixMap (a*c) (b*d) => f X) h


/-- Every repeated local channel is permutation covariant, not only unitary channels. -/
theorem permute_power_map (Φ : KrausChannel a b) (n : ℕ) (π : Equiv.Perm (Fin n)) :
    (permuteChannel n π (Φ.tensorPower n)).toLinearMap = (Φ.tensorPower n).toLinearMap := by
  apply MatrixMap.choi_injective
  simp only [MatrixMap.choi_toLinearMap,permuteChannel,reindexChannel_choi]
  ext ⟨i,x⟩ ⟨j,y⟩
  obtain ⟨i,rfl⟩ := (channelIndexEquiv a n).surjective i
  obtain ⟨j,rfl⟩ := (channelIndexEquiv a n).surjective j
  obtain ⟨x,rfl⟩ := (channelIndexEquiv b n).surjective x
  obtain ⟨y,rfl⟩ := (channelIndexEquiv b n).surjective y
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.prodCongr_symm,
    Equiv.prodCongr_apply,sitePermutation,Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm,
    Prod.map_apply,Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  simp only [choi_tensorPower_apply,TensorPermutation.factorPermutation_symm_coordinates]
  exact Equiv.prod_comp π (fun l => Φ.choi
    (TensorPower.indexEquiv (Fin a) n i l,TensorPower.indexEquiv (Fin b) n x l)
    (TensorPower.indexEquiv (Fin a) n j l,TensorPower.indexEquiv (Fin b) n y l))

theorem power_permutation_apply (Φ : KrausChannel a b) (n : ℕ) (π : Equiv.Perm (Fin n))
    (X : Operator (a^n)) :
    (Φ.tensorPower n).apply (Matrix.reindex (sitePermutation a n π) (sitePermutation a n π) X) =
      Matrix.reindex (sitePermutation b n π) (sitePermutation b n π) ((Φ.tensorPower n).apply X) := by
  have h := reindexChannel_apply (sitePermutation a n π) (sitePermutation b n π) (Φ.tensorPower n) X
  change (permuteChannel n π (Φ.tensorPower n)).toLinearMap _ = _ at h
  rw [permute_power_map] at h
  exact h

/-- Applying independent channel copies to independent states gives independent outputs. -/
theorem tensorPower_onState (Φ : KrausChannel a b) (τ : State a) (n : ℕ) :
    (Φ.tensorPower n).onState (statePower τ n) = statePower (Φ.onState τ) n := by
  induction n with
  | zero => exact ParallelBlockTests.state_one_unique _ _
  | succ n ih =>
    apply State.eq_of_matrix_eq
    rw [StatePowerRenyi.statePower_succ,StatePowerRenyi.statePower_succ]
    change ((Φ.tensor (Φ.tensorPower n)).cast _ _).apply
      (Matrix.reindex (finCongr _) (finCongr _) (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (τ.matrix ⊗ₖ (statePower τ n).matrix))) = _
    rw [KrausChannel.cast_apply,KrausChannel.tensor_apply_product]
    have h := congrArg State.matrix ih
    change (Φ.tensorPower n).apply (statePower τ n).matrix = (statePower (Φ.onState τ) n).matrix at h
    rw [h]
    rfl

/-- Covariance with respect to an arbitrary indexed family of local channel actions. -/
def covariantFamily {G : Type*} (U : G → KrausChannel a a) (V : G → KrausChannel b b) :
    AlternativeFamily a b := fun n => {Φ | IsChannel Φ ∧ ∀ g X,
      Φ ((U g).tensorPower n |>.apply X) = ((V g).tensorPower n).apply (Φ X)}

def covarianceChoiConstraint {G : Type*} (U : G → KrausChannel a a) (V : G → KrausChannel b b)
    (n : ℕ) (C : TestingSDP.BipartiteOperator (a^n) (b^n)) : Prop :=
  ∀ g X, choiAction C (((U g).tensorPower n).apply X) =
    ((V g).tensorPower n).apply (choiAction C X)

theorem covariance_choi_image {G : Type*} (U : G → KrausChannel a a) (V : G → KrausChannel b b) (n : ℕ) :
    MatrixMap.choi '' covariantFamily U V n = channelChoiSet (a^n) (b^n) ∩
      {C | covarianceChoiConstraint U V n C} := by
  apply channelSlice_choi_image
  intro Φ
  simp only [covarianceChoiConstraint,choiAction_choi]

theorem isClosed_covarianceChoiConstraint {G : Type*} (U : G → KrausChannel a a)
    (V : G → KrausChannel b b) (n : ℕ) :
    IsClosed {C | covarianceChoiConstraint U V n C} := by
  have he : {C | covarianceChoiConstraint U V n C} =
      ⋂ g, ⋂ X, {C | choiAction C (((U g).tensorPower n).apply X) =
        ((V g).tensorPower n).apply (choiAction C X)} := by ext C; simp [covarianceChoiConstraint]
  rw [he]
  apply isClosed_iInter; intro g
  apply isClosed_iInter; intro X
  apply isClosed_eq (continuous_choiAction _)
  exact (((V g).tensorPower n).toLinearMap.continuous_of_finiteDimensional).comp (continuous_choiAction _)

theorem convex_covarianceChoiConstraint {G : Type*} (U : G → KrausChannel a a)
    (V : G → KrausChannel b b) (n : ℕ) :
    Convex ℝ {C | covarianceChoiConstraint U V n C} := by
  intro C hC D hD r s hr hs hrs
  intro g X
  rw [choiAction_mix,choiAction_mix,hC,hD]
  change _ = ((V g).tensorPower n).toLinearMap (r • choiAction C X+s • choiAction D X)
  simp only [map_add,LinearMap.map_smul_of_tower]
  rfl

/-- The faithful output replacer intertwines whenever the output witness is invariant. -/
theorem replacer_mem_covariant {G : Type*} (U : G → KrausChannel a a) (V : G → KrausChannel b b)
    (ω : State b) (hω : ∀ g, (V g).onState ω = ω) (n : ℕ) :
    ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ covariantFamily U V n := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  intro g X
  rw [ReplacerChannel.tensorPower_map]
  change (((U g).tensorPower n).apply X).trace • (statePower ω n).matrix =
    ((V g).tensorPower n).toLinearMap (X.trace • (statePower ω n).matrix)
  rw [KrausChannel.trace_apply,map_smul]
  have h := congrArg State.matrix (tensorPower_onState (V g) ω n)
  rw [hω] at h
  change ((V g).tensorPower n).apply (statePower ω n).matrix = _ at h
  change X.trace • (statePower ω n).matrix = X.trace • ((V g).tensorPower n).apply (statePower ω n).matrix
  rw [h]


/-- Unrestricted evaluation formula for channel coordinate changes. -/
theorem reindexChannel_apply_any {c d : ℕ} (ea : Fin a ≃ Fin c) (eb : Fin b ≃ Fin d)
    (Φ : KrausChannel a b) (X : Operator c) :
    (reindexChannel ea eb Φ).apply X =
      Matrix.reindex eb eb (Φ.apply (Matrix.reindex ea.symm ea.symm X)) := by
  have h := reindexChannel_apply ea eb Φ (Matrix.reindex ea.symm ea.symm X)
  simpa only [Matrix.reindex_apply,Matrix.submatrix_submatrix,Function.comp_def,
    Equiv.symm_apply_apply,Matrix.submatrix_id_id] using h

theorem power_add_inverse_apply (Φ : KrausChannel a b) (n m : ℕ) (X : Operator (a^(n+m))) :
    Matrix.reindex (channelAddEquiv b n m).symm (channelAddEquiv b n m).symm
      ((Φ.tensorPower (n+m)).apply X) =
    ((Φ.tensorPower n).tensor (Φ.tensorPower m)).apply
      (Matrix.reindex (channelAddEquiv a n m).symm (channelAddEquiv a n m).symm X) := by
  have h := tensorPower_add_apply Φ n m
    (Matrix.reindex (channelAddEquiv a n m).symm (channelAddEquiv a n m).symm X)
  have h' := congrArg (Matrix.reindex (channelAddEquiv b n m).symm (channelAddEquiv b n m).symm) h
  simpa only [Matrix.reindex_apply,Matrix.submatrix_submatrix,Function.comp_def,
    Equiv.symm_apply_apply,Equiv.apply_symm_apply,Matrix.submatrix_id_id] using h'

theorem covariant_tensor {G : Type*} (U : G → KrausChannel a a) (V : G → KrausChannel b b)
    (n m : ℕ) (Φ : KrausChannel (a^n) (b^n)) (Ψ : KrausChannel (a^m) (b^m))
    (hΦ : Φ.toLinearMap ∈ covariantFamily U V n) (hΨ : Ψ.toLinearMap ∈ covariantFamily U V m) :
    (tensorBlocks n m Φ Ψ).toLinearMap ∈ covariantFamily U V (n+m) := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  intro g X
  change (tensorBlocks n m Φ Ψ).apply _ = ((V g).tensorPower (n+m)).apply ((tensorBlocks n m Φ Ψ).apply X)
  simp only [tensorBlocks,reindexChannel_apply_any,power_add_inverse_apply]
  rw [tensor_intertwines Φ Ψ _ _ _ _ (hΦ.2 g) (hΨ.2 g)]
  exact (tensorPower_add_apply (V g) n m _).symm

theorem covariant_permutation {G : Type*} (U : G → KrausChannel a a) (V : G → KrausChannel b b)
    (n : ℕ) (π : Equiv.Perm (Fin n)) (Φ : KrausChannel (a^n) (b^n))
    (hΦ : Φ.toLinearMap ∈ covariantFamily U V n) :
    (permuteChannel n π Φ).toLinearMap ∈ covariantFamily U V n := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  intro g X
  obtain ⟨X,rfl⟩ := (Matrix.reindexLinearEquiv ℂ ℂ (sitePermutation a n π) (sitePermutation a n π)).surjective X
  change (permuteChannel n π Φ).apply ((U g).tensorPower n |>.apply (Matrix.reindex _ _ X)) =
    ((V g).tensorPower n).apply ((permuteChannel n π Φ).apply (Matrix.reindex _ _ X))
  rw [power_permutation_apply]
  simp only [permuteChannel,reindexChannel_apply]
  change Matrix.reindex _ _ (Φ.toLinearMap (((U g).tensorPower n).apply X)) = _
  rw [hΦ.2]
  exact (power_permutation_apply (V g) n π _).symm

/-- Partial trace intertwines all local trace-preserving output actions. -/
theorem discard_tensor_apply {d e : ℕ} (B : KrausChannel d d) (D : KrausChannel e e)
    (X : Operator (d*e)) :
    (discardRight d e).apply ((B.tensor D).apply X) =
      B.apply ((discardRight d e).apply X) := by
  have h := matrixMap_ext_product
    ((discardRight d e).toLinearMap.comp (B.tensor D).toLinearMap)
    (B.toLinearMap.comp (discardRight d e).toLinearMap) (fun Y Z => by
      change (discardRight d e).apply ((B.tensor D).apply _) = B.apply ((discardRight d e).apply _)
      rw [KrausChannel.tensor_apply_product,discardRight_apply_product,discardRight_apply_product,
        KrausChannel.trace_apply]
      exact (B.toLinearMap.map_smul Z.trace Y).symm)
  exact congrArg (fun f : MatrixMap (d*e) d => f X) h

/-- Appending an invariant state intertwines the corresponding local input actions. -/
theorem append_intertwines {d e : ℕ} (A : KrausChannel d d) (C : KrausChannel e e)
    (τ : State e) (hτ : C.onState τ=τ) (X : Operator d) :
    (A.tensor C).apply ((appendState d τ).apply X) = (appendState d τ).apply (A.apply X) := by
  rw [appendState_apply,KrausChannel.tensor_apply_product,appendState_apply]
  have h := congrArg State.matrix hτ
  change C.apply τ.matrix = τ.matrix at h
  rw [h]

theorem covariant_marginal {G : Type*} (U : G → KrausChannel a a) (V : G → KrausChannel b b)
    (τ : State a) (hτ : ∀ g, (U g).onState τ=τ) (n : ℕ)
    (Φ : KrausChannel (a^(n+1)) (b^(n+1))) (hΦ : Φ.toLinearMap ∈ covariantFamily U V (n+1)) :
    (marginalChannel n τ Φ).toLinearMap ∈ covariantFamily U V n := by
  refine ⟨(isChannel_iff_kraus _).mpr ⟨_,rfl⟩,?_⟩
  intro g X
  let Ψ := reindexChannel (channelAddEquiv a n 1).symm (channelAddEquiv b n 1).symm Φ
  have hΨ (Y : Operator (a^n*a^1)) :
      Ψ.apply (((U g).tensorPower n).tensor ((U g).tensorPower 1) |>.apply Y) =
      (((V g).tensorPower n).tensor ((V g).tensorPower 1)).apply (Ψ.apply Y) := by
    simp only [Ψ,reindexChannel_apply_any,Equiv.symm_symm]
    rw [← tensorPower_add_apply]
    change Matrix.reindex _ _ (Φ.toLinearMap (((U g).tensorPower (n+1)).apply _)) = _
    rw [hΦ.2,power_add_inverse_apply]
    rfl
  have hτ1 : ((U g).tensorPower 1).onState (statePower τ 1) = statePower τ 1 := by
    rw [tensorPower_onState,hτ]
  change (marginalChannel n τ Φ).apply _ = ((V g).tensorPower n).apply ((marginalChannel n τ Φ).apply X)
  simp only [marginalChannel,KrausChannel.compose_apply]
  change (discardRight _ _).apply (Ψ.apply ((appendState (a^n) (statePower τ 1)).apply (((U g).tensorPower n).apply X))) = _
  rw [← append_intertwines _ _ _ hτ1,hΨ,discard_tensor_apply]

/-- Compactness, convexity and tensor closure of all block intertwiners. -/
theorem covariant_admissible {G : Type*} (U : G → KrausChannel a a) (V : G → KrausChannel b b)
    (ω : State b) (hω : ω.matrix.PosDef) (hωinv : ∀ g, (V g).onState ω=ω) :
    Admissible (covariantFamily U V) where
  channels n hn Φ hΦ := hΦ.1
  nonempty n hn := ⟨_,replacer_mem_covariant U V ω hωinv n⟩
  compact n hn := by
    rw [covariance_choi_image]
    exact (isCompact_channelChoiSet _ _).inter_right (isClosed_covarianceChoiConstraint U V n)
  convex n hn := by
    rw [covariance_choi_image]
    exact (convex_channelChoiSet _ _).inter (convex_covarianceChoiConstraint U V n)
  tensor_closed n m hn hm Φ Ψ hΦ hΨ := covariant_tensor U V n m Φ Ψ hΦ hΨ
  faithful_replacer := ⟨ω,hω,replacer_mem_covariant U V ω hωinv 1⟩

theorem covariant_quantitative {G : Type*} (U : G → KrausChannel a a) (V : G → KrausChannel b b)
    (τ : State a) (hτ : τ.matrix.PosDef) (hτinv : ∀ g, (U g).onState τ=τ) :
    QuantitativeAt (covariantFamily U V) τ where
  faithful := hτ
  permutation_closed n hn π Φ hΦ := covariant_permutation U V n π Φ hΦ
  marginal_closed n hn Φ hΦ := covariant_marginal U V τ hτinv n Φ hΦ

/-- Literal group-unitary specialization, with no finiteness or compactness requirement on the group. -/
def unitaryCovariantFamily {G : Type*} [Group G]
    (U : G →* Matrix.unitaryGroup (Fin a) ℂ) (V : G →* Matrix.unitaryGroup (Fin b) ℂ) :
    AlternativeFamily a b := covariantFamily
      (fun g => SharpDivergence.unitaryChannel (U g)) (fun g => SharpDivergence.unitaryChannel (V g))

/-- Proposition 21's covariance part; the intersection part is `intersection_admissible`
and `intersection_quantitative`, including empty intersections in the CPTP ambient space. -/
theorem proposition_21 {G : Type*} [Group G]
    (U : G →* Matrix.unitaryGroup (Fin a) ℂ) (V : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (τ : State a) (ω : State b) (hτ : τ.matrix.PosDef) (hω : ω.matrix.PosDef)
    (hτinv : ∀ g, (U g).val*τ.matrix*(U g).valᴴ=τ.matrix)
    (hωinv : ∀ g, (V g).val*ω.matrix*(V g).valᴴ=ω.matrix) :
    Admissible (unitaryCovariantFamily U V) ∧ QuantitativeAt (unitaryCovariantFamily U V) τ := by
  constructor
  · apply covariant_admissible _ _ ω hω
    intro g
    apply State.eq_of_matrix_eq
    exact (SharpDivergence.unitaryChannel_apply _ _).trans (hωinv g)
  · apply covariant_quantitative _ _ τ hτ
    intro g
    apply State.eq_of_matrix_eq
    exact (SharpDivergence.unitaryChannel_apply _ _).trans (hτinv g)

end GeneralizedChannelStein
