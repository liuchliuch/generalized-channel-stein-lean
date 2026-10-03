import GeneralizedChannelStein.BranchExtraction
import GeneralizedChannelStein.ChannelSpace
import QuantumChannelStein.ChannelComposition
import QuantumChannelStein.AdaptiveCircuit

/-! # Actual auxiliary-output extensions and their operational tests -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.AuxiliaryExtensions
open QuantumChannelStein Matrix ChannelEntropy ChannelPowerReindex OperationalTesting
  BranchExtraction
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b e : ℕ}

def discardKraus (b e : ℕ) (j : Fin e) : Matrix (Fin b) (Fin (b*e)) ℂ :=
  fun i x => if (finProdFinEquiv.symm x).1=i ∧ (finProdFinEquiv.symm x).2=j then 1 else 0

theorem discardKraus_normalized (b e : ℕ) :
    ∑ j : Fin e, (discardKraus b e j)ᴴ * discardKraus b e j = 1 := by
  ext x y
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨k,l⟩,rfl⟩ := finProdFinEquiv.surjective y
  simp [discardKraus,Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.one_apply,finProdFinEquiv.injective.eq_iff,Prod.mk.injEq,ite_and]
  split_ifs <;> simp

def discard (b e : ℕ) : KrausChannel (b*e) b where
  rank := e
  kraus := discardKraus b e
  normalized := discardKraus_normalized b e

/-- Discard is literally partial trace in the specified product coordinates. -/
theorem discard_apply (X : Operator (b*e)) :
    (discard b e).apply X = KrausChannel.traceEnvironment
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm X) := by
  ext i j
  have hd (x : Fin b) (y : Fin e) : (finProdFinEquiv (x,y)).divNat=x :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (x,y))
  have hm (x : Fin b) (y : Fin e) : (finProdFinEquiv (x,y)).modNat=y :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (x,y))
  simp [discard,KrausChannel.apply,discardKraus,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.sum_apply,KrausChannel.traceEnvironment,Matrix.reindex_apply,
    ← finProdFinEquiv.sum_comp,Fintype.sum_prod_type,ite_and,hd,hm,apply_ite]

/-- Output reduction of every candidate extension is an actual CPTP channel. -/
def reduced (L : KrausChannel a (b*e)) : KrausChannel a b := (discard b e).compose L

/-- The extension set is the literal inverse image under output partial trace. -/
def extensionFamily (F : Set (MatrixMap a b)) : Set (MatrixMap a (b*e)) :=
  {L | IsChannel L ∧ ((discard b e).toLinearMap.comp L) ∈ F}

theorem reduced_map (L : KrausChannel a (b*e)) :
    (reduced L).toLinearMap = (discard b e).toLinearMap.comp L.toLinearMap := by
  ext X i j
  exact congrFun (congrFun (KrausChannel.compose_apply (discard b e) L X) i) j

theorem extension_mem_iff (F : Set (MatrixMap a b)) (L : KrausChannel a (b*e)) :
    L.toLinearMap ∈ extensionFamily F ↔ (reduced L).toLinearMap ∈ F := by
  change (IsChannel L.toLinearMap ∧ _) ↔ _
  rw [← reduced_map]
  simp only [and_iff_right_iff_imp]
  intro _
  exact (isChannel_iff_kraus _).mpr ⟨L,rfl⟩

theorem amplify_compose {c : ℕ} (P : KrausChannel b c) (Q : KrausChannel a b)
    (r : ℕ) (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    (P.compose Q).amplify r X = P.amplify r (Q.amplify r X) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  rw [KrausChannel.amplify_block,KrausChannel.amplify_block,KrausChannel.compose_apply]
  congr 1
  ext k l
  exact (Q.amplify_block r X i j k l).symm

theorem outputState_compose {c : ℕ} (P : KrausChannel b c) (Q : KrausChannel a b)
    (r : ℕ) (ρ : State (r*a)) :
    outputState (P.compose Q) r ρ = outputState P r (outputState Q r ρ) := by
  apply State.eq_of_matrix_eq
  dsimp [outputState]
  rw [amplify_compose]
  congr 2
  ext i j
  simp [Matrix.reindex_apply,Matrix.submatrix_submatrix]

/-- Lift an original tester by its actual Heisenberg effect pullback. -/
def liftTest (t : ChannelTest a b) : ChannelTest a (b*e) where
  reference := t.reference
  input := t.input
  effect := (((KrausChannel.identity t.reference).tensor (discard b e)).pullbackEffect t.effect)

theorem liftTest_acceptance (t : ChannelTest a b) (L : KrausChannel a (b*e)) :
    (liftTest t).acceptance L=t.acceptance (reduced L) := by
  change (((KrausChannel.identity t.reference).tensor (discard b e)).pullbackEffect t.effect).probability
    (outputState L t.reference t.input) = _
  rw [KrausChannel.pullbackEffect_probability,← ChannelLocality.outputState_eq_tensor,
    ← outputState_compose]
  rfl

theorem acceptance_congr (t : ChannelTest a b) (N M : KrausChannel a b)
    (h : N.toLinearMap=M.toLinearMap) : t.acceptance N=t.acceptance M := by
  have hout : outputState N t.reference t.input=outputState M t.reference t.input := by
    apply State.eq_of_matrix_eq
    dsimp [outputState]
    congr 1
    rw [← MatrixMap.amplify_toLinearMap,← MatrixMap.amplify_toLinearMap,h]
  exact congrArg t.effect.probability hout

/-- The upper comparison in Lemma26: discarding auxiliary access cannot
improve a test, for the entire alternative family at once. -/
theorem extensionBeta_le_original (N : KrausChannel a b) (V : KrausChannel a (b*e))
    (hV : (reduced V).toLinearMap=N.toLinearMap) (F : Set (MatrixMap a b)) (ε : ℝ) :
    compositeBeta V (extensionFamily F) ε≤compositeBeta N F ε := by
  apply le_iInf
  intro t
  have hp : 1-ε≤(liftTest t.val).acceptance V := by
    rw [liftTest_acceptance,acceptance_congr t.val (reduced V) N hV]
    exact t.property
  apply (iInf_le_of_le ⟨liftTest t.val,hp⟩ le_rfl).trans
  apply iSup_le
  intro L
  rw [liftTest_acceptance]
  exact le_iSup_of_le ⟨reduced L.val,(extension_mem_iff F L.val).mp L.property⟩ le_rfl

/-- Forgetting the output of a local environment channel preserves the other marginal. -/
theorem discard_local_channel {f : ℕ} (E : KrausChannel f e) (X : Operator (b*f)) :
    (discard b e).apply (((KrausChannel.identity b).tensor E).apply X)=(discard b f).apply X := by
  let Y := Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm X
  have hX : X=Matrix.reindex finProdFinEquiv finProdFinEquiv Y := by
    ext i j
    change X i j = X (finProdFinEquiv (finProdFinEquiv.symm i)) (finProdFinEquiv (finProdFinEquiv.symm j))
    simp only [Equiv.apply_symm_apply]
  rw [hX,ChannelLocality.identity_tensor_apply_reindex,discard_apply,discard_apply]
  have hinv {n m : ℕ} (T : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
      Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (Matrix.reindex finProdFinEquiv finProdFinEquiv T)=T := by
    ext i j
    change T (finProdFinEquiv.symm (finProdFinEquiv i)) (finProdFinEquiv.symm (finProdFinEquiv j))=T i j
    simp only [Equiv.symm_apply_apply]
  rw [hinv,hinv]
  ext i j
  change (∑ k : Fin e, E.amplify b Y (i,k) (j,k)) = ∑ k : Fin f, Y (i,k) (j,k)
  simp_rw [E.amplify_block]
  exact E.trace_apply (fun k l => Y (i,k) (j,l))

/-- Flatten the physical output and environment into a single output index. -/
def outputIsometry (V : Matrix (Fin b × Fin e) (Fin a) ℂ) : Matrix (Fin (b*e)) (Fin a) ℂ :=
  Matrix.reindex finProdFinEquiv (Equiv.refl _) V

theorem outputIsometry_isometry (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) :
    (outputIsometry V)ᴴ * outputIsometry V=1 := ChannelDilationPower.reindex_isometry _ _ _ hV

theorem outputIsometry_norm (V : Matrix (Fin b × Fin e) (Fin a) ℂ) :
    ‖outputIsometry V‖=‖V‖ := TensorPower.norm_reindex _ _ _

theorem discard_adMap (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (X : Operator a) :
    (discard b e).apply (adMap (outputIsometry V) X)=dilationMap V X := by
  rw [adMap_apply,discard_apply,dilationMap_apply]
  congr 1
  ext ⟨i,k⟩ ⟨j,l⟩
  simp [outputIsometry,Matrix.reindex_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]

/-- Reducing the actual isometric target recovers the prescribed noisy channel. -/
theorem reduced_isometry_map (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) :
    (reduced (isometryChannel (outputIsometry V) (outputIsometry_isometry V hV))).toLinearMap =
      dilationMap V := by
  rw [reduced_map,isometryChannel_map]
  ext X i j
  exact congrFun (congrFun (discard_adMap V X) i) j

/-- Every channel on the original Stinespring environment produces an actual
extension, uniformly on all inputs. -/
def environmentalExtension (M : KrausChannel a b) (E : KrausChannel M.rank e) : KrausChannel a (b*e) :=
  ((KrausChannel.identity b).tensor E).compose
    (isometryChannel (outputIsometry M.stinespring)
      (outputIsometry_isometry M.stinespring M.stinespring_isometry))

theorem environmentalExtension_reduced (M : KrausChannel a b) (E : KrausChannel M.rank e) :
    (reduced (environmentalExtension M E)).toLinearMap=M.toLinearMap := by
  ext X i j
  change (reduced (environmentalExtension M E)).apply X i j = M.apply X i j
  simp only [reduced,environmentalExtension,KrausChannel.compose_apply]
  rw [show (isometryChannel (outputIsometry M.stinespring)
    (outputIsometry_isometry M.stinespring M.stinespring_isometry)).apply X =
      adMap (outputIsometry M.stinespring) X from rfl]
  change (discard b e).apply (((KrausChannel.identity b).tensor E).apply
    (adMap (outputIsometry M.stinespring) X)) i j = M.apply X i j
  rw [discard_local_channel,discard_adMap,ParallelConverse.dilationMap_stinespring]
  rfl

/-- Every individual Kraus operator is a genuine CP branch of its channel. -/
theorem single_kraus_cpLe {a b : ℕ} (M : KrausChannel a b) (i : Fin M.rank) :
    MatrixMap.CPLe (adMap (M.kraus i)) M.toLinearMap := by
  intro r X hX
  have heq : MatrixMap.amplify (M.toLinearMap-adMap (M.kraus i)) r X =
      M.amplify r X-MatrixMap.amplify (adMap (M.kraus i)) r X := by
    change MatrixMap.amplify M.toLinearMap r X-_=_
    rw [MatrixMap.amplify_toLinearMap]
    rfl
  rw [heq,adMap,MatrixMap.amplify_ofKraus]
  simp only [Fin.sum_univ_one]
  change ((∑ j : Fin M.rank, ((1:Operator r) ⊗ₖ M.kraus j)*X*((1:Operator r) ⊗ₖ M.kraus j)ᴴ)-
    ((1:Operator r) ⊗ₖ M.kraus i)*X*((1:Operator r) ⊗ₖ M.kraus i)ᴴ).PosSemidef
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),add_sub_cancel_right]
  apply Matrix.posSemidef_sum
  intro j hj
  exact hX.mul_mul_conjTranspose_same _

/-- Completing a contraction on the environment leaves its designated Kraus
operator as an explicit physical branch of the extension channel. -/
theorem environmentalExtension_branch (M : KrausChannel a b)
    (A : Matrix (Fin e) (Fin M.rank) ℂ) (hA : ‖A‖≤1) (z : Fin e) :
    MatrixMap.CPLe (adMap (outputIsometry (EnvironmentTensor.applyEnvironment M.stinespring A)))
      (environmentalExtension M (KrausRecovery.channel A hA z)).toLinearMap := by
  let E := KrausRecovery.channel A hA z
  let i : Fin (environmentalExtension M E).rank :=
    finProdFinEquiv (finProdFinEquiv ((0 : Fin 1),Fin.castAdd M.rank (0 : Fin 1)),(0 : Fin 1))
  have hi : (environmentalExtension M E).kraus i =
      outputIsometry (EnvironmentTensor.applyEnvironment M.stinespring A) := by
    dsimp only [environmentalExtension,KrausChannel.compose,i,KrausChannel.tensor,
      KrausChannel.tensorKraus,KrausChannel.identity,isometryChannel,E,KrausRecovery.channel]
    simp only [Equiv.symm_apply_apply,Fin.addCases_left]
    change Matrix.reindex finProdFinEquiv finProdFinEquiv ((1:Operator b) ⊗ₖ A) *
      Matrix.reindex finProdFinEquiv (Equiv.refl _) M.stinespring =
      Matrix.reindex finProdFinEquiv (Equiv.refl _) (((1:Operator b) ⊗ₖ A)*M.stinespring)
    exact (Matrix.reindexLinearEquiv_mul ℂ ℂ finProdFinEquiv finProdFinEquiv (Equiv.refl _)
      ((1:Operator b) ⊗ₖ A) M.stinespring)
  simpa only [hi] using single_kraus_cpLe (environmentalExtension M E) i

/-- A nonzero-input isometry has a nonempty output environment. -/
theorem environment_pos (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) (ha : 0<a) :
    0<e := by
  by_contra he
  have he0 : e=0 := by omega
  subst e
  have h := congrFun (congrFun hV (⟨0,ha⟩ : Fin a)) ⟨0,ha⟩
  simp [Matrix.mul_apply] at h

/-- One actual extension contains a scaled CP branch uniformly close to the
prescribed Stinespring isometry. This bypasses pointwise extension oracles. -/
theorem extension_with_close_branch (N M : KrausChannel a b) (ha : 0<a)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1)
    (hVN : dilationMap V=N.toLinearMap) (ε β : ℝ)
    (hε : 0<ε) (hε1 : ε<1) (hβ : 0<β)
    (hb : ENNReal.ofReal β≤singleBeta N M ε) :
    ∃ L : KrausChannel a (b*e), ∃ Z : Matrix (Fin (b*e)) (Fin a) ℂ,
      (reduced L).toLinearMap=M.toLinearMap ∧
      MatrixMap.CPLe (adMap Z) (Complex.ofReal (ε/β) • L.toLinearMap) ∧
      ‖outputIsometry V-Z‖≤Real.sqrt (1-ε) := by
  let t := ε/β
  have ht : 0<t := div_pos hε hβ
  have hs : 0<Real.sqrt t := Real.sqrt_pos.mpr ht
  obtain ⟨A,hA,he⟩ := rough_auxiliary_map N M ha V M.stinespring hVN
    (ParallelConverse.dilationMap_stinespring M) ε β hε.le hβ hb
  let B := (Real.sqrt t)⁻¹ • A
  have hB : ‖B‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hs.le)]
    exact (mul_le_mul_of_nonneg_left hA (inv_nonneg.mpr hs.le)).trans_eq (inv_mul_cancel₀ hs.ne')
  let z : Fin e := ⟨0,environment_pos V hV ha⟩
  let L := environmentalExtension M (KrausRecovery.channel B hB z)
  let Z := outputIsometry (EnvironmentTensor.applyEnvironment M.stinespring A)
  refine ⟨L,Z,environmentalExtension_reduced M _,?_,?_⟩
  · have h := environmentalExtension_branch M B hB z
    have hZ : outputIsometry (EnvironmentTensor.applyEnvironment M.stinespring B)=(Real.sqrt t)⁻¹ • Z := by
      ext i j
      simp [Z,B,outputIsometry,EnvironmentTensor.applyEnvironment,Matrix.reindex_apply,
        Matrix.kronecker_smul,Matrix.smul_mul]
    rw [hZ,adMap_real_smul] at h
    have h' := FreeAmplification.cpLe_smul_real h t ht.le
    have htroot : t*((Real.sqrt t)⁻¹)^2=1 := by
      rw [inv_pow,Real.sq_sqrt ht.le,mul_inv_cancel₀ ht.ne']
    simpa only [smul_smul,← Complex.ofReal_mul,htroot,Complex.ofReal_one,one_smul] using h'
  · have heq : outputIsometry V-Z=outputIsometry (V-EnvironmentTensor.applyEnvironment M.stinespring A) := rfl
    rw [heq,outputIsometry_norm]
    have hr : (Real.sqrt (1-ε))^2=1-ε := Real.sq_sqrt (by linarith)
    change ‖V-EnvironmentTensor.applyEnvironment M.stinespring A‖^2≤1-ε at he
    nlinarith [norm_nonneg (V-EnvironmentTensor.applyEnvironment M.stinespring A),Real.sqrt_nonneg (1-ε)]

/-- Choi-coordinate partial trace of only the newly accessible auxiliary output. -/
def discardChoi : TestingSDP.BipartiteOperator a (b*e) →ₗ[ℝ] TestingSDP.BipartiteOperator a b where
  toFun X := fun (i j : Fin a × Fin b) => ∑ z : Fin e, X (i.1,finProdFinEquiv (i.2,z)) (j.1,finProdFinEquiv (j.2,z))
  map_add' X Y := by ext i j; simp [Finset.sum_add_distrib]
  map_smul' c X := by ext i j; simp [Finset.smul_sum]

theorem continuous_discardChoi : Continuous (discardChoi (a:=a) (b:=b) (e:=e)) := by
  change Continuous (fun X : TestingSDP.BipartiteOperator a (b*e) =>
    fun (i j : Fin a × Fin b) => ∑ z : Fin e, X (i.1,finProdFinEquiv (i.2,z)) (j.1,finProdFinEquiv (j.2,z)))
  fun_prop

theorem choi_discard_comp (L : MatrixMap a (b*e)) :
    MatrixMap.choi ((discard b e).toLinearMap.comp L)=discardChoi (MatrixMap.choi L) := by
  ext ⟨i,u⟩ ⟨j,v⟩
  change (discard b e).apply (L (Matrix.single i j 1)) u v = _
  rw [discard_apply]
  rfl

theorem extensionFamily_choi_image (F : Set (MatrixMap a b)) :
    MatrixMap.choi '' (extensionFamily (e:=e) F) =
      channelChoiSet a (b*e) ∩ (discardChoi ⁻¹' (MatrixMap.choi '' F)) := by
  ext C
  constructor
  · rintro ⟨L,⟨hL,hF⟩,rfl⟩
    constructor
    · rw [channelChoiSet_eq_image]
      exact ⟨L,hL,rfl⟩
    · exact ⟨_,hF,choi_discard_comp L⟩
  · rintro ⟨hC,hF⟩
    rw [channelChoiSet_eq_image] at hC
    obtain ⟨L,hL,rfl⟩ := hC
    obtain ⟨M,hM,he⟩ := hF
    refine ⟨L,⟨hL,?_⟩,rfl⟩
    have heq : M=(discard b e).toLinearMap.comp L := MatrixMap.choi_injective
      (he.trans (choi_discard_comp L).symm)
    rwa [← heq]

theorem extensionFamily_compact (F : Set (MatrixMap a b))
    (hF : IsCompact (MatrixMap.choi '' F)) :
    IsCompact (MatrixMap.choi '' (extensionFamily (e:=e) F)) := by
  rw [extensionFamily_choi_image]
  exact (isCompact_channelChoiSet _ _).inter_right (hF.isClosed.preimage continuous_discardChoi)

theorem extensionFamily_convex (F : Set (MatrixMap a b))
    (hF : Convex ℝ (MatrixMap.choi '' F)) :
    Convex ℝ (MatrixMap.choi '' (extensionFamily (e:=e) F)) := by
  rw [extensionFamily_choi_image]
  exact (convex_channelChoiSet _ _).inter (hF.linear_preimage discardChoi)

theorem extensionFamily_nonempty (F : Set (MatrixMap a b))
    (hF : ∀ M ∈ F, IsChannel M) (hne : F.Nonempty) (he : 0<e) :
    (extensionFamily (e:=e) F).Nonempty := by
  obtain ⟨P,hP⟩ := hne
  obtain ⟨M,rfl⟩ := (isChannel_iff_kraus P).mp (hF P hP)
  let E := KrausRecovery.channel (0 : Matrix (Fin e) (Fin M.rank) ℂ) (by simp) ⟨0,he⟩
  refine ⟨(environmentalExtension M E).toLinearMap,?_⟩
  apply (extension_mem_iff F _).mpr
  rw [environmentalExtension_reduced]
  exact hP

end GeneralizedChannelStein.AuxiliaryExtensions
