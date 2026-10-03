import GeneralizedChannelStein.SymmetrizedBranch
import GeneralizedChannelStein.DilationTensor

/-! Coherent contraction of an actual weighted input/output marginal. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace GeneralizedChannelStein.CoherentMarginal
open QuantumChannelStein Matrix ChannelEntropy BranchExtraction
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b c d e : ℕ}

def prepareEquiv (a c e : ℕ) : Fin a × (Fin c × Fin e) ≃ Fin (a*c) × Fin e :=
  (Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr finProdFinEquiv (Equiv.refl _))

/-- Identity on the retained input tensored with a normalized preparation vector. -/
def preparation (a : ℕ) (P : Matrix (Fin c × Fin e) (Fin 1) ℂ) :
    Matrix (Fin (a*c) × Fin e) (Fin a) ℂ :=
  Matrix.reindex (prepareEquiv a c e) (Equiv.prodUnique (Fin a) (Fin 1)) ((1:Operator a) ⊗ₖ P)

theorem preparation_apply (P : Matrix (Fin c × Fin e) (Fin 1) ℂ)
    (x i : Fin a) (u : Fin c) (v : Fin e) :
    preparation a P (finProdFinEquiv (i,u),v) x=(if i=x then 1 else 0)*P (u,v) 0 := by
  simp [preparation,prepareEquiv,Matrix.reindex_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]

theorem preparation_norm (P : Matrix (Fin c × Fin e) (Fin 1) ℂ) :
    ‖preparation a P‖≤‖P‖ := by
  rw [preparation,TensorPower.norm_reindex]
  exact TensorNorm.one_kronecker_opNorm_le P

theorem preparation_isometry (P : Matrix (Fin c × Fin e) (Fin 1) ℂ) (hP : Pᴴ*P=1) :
    (preparation a P)ᴴ*preparation a P=1 := by
  apply ChannelDilationPower.reindex_isometry
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,Matrix.conjTranspose_one,
    Matrix.one_mul,hP,Matrix.one_kronecker_one]

theorem preparation_map (P : Matrix (Fin c × Fin e) (Fin 1) ℂ) (X : Operator a) :
    dilationMap (preparation a P) X = Matrix.reindex finProdFinEquiv finProdFinEquiv
      (X ⊗ₖ dilationMap P 1) := by
  ext i j
  obtain ⟨⟨x,u⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨y,v⟩,rfl⟩ := finProdFinEquiv.surjective j
  simp [dilationMap,MatrixMap.ofKraus,Matrix.sum_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,preparation_apply,Matrix.reindex_apply,Matrix.kroneckerMap_apply,
    Finset.mul_sum,Finset.sum_mul,mul_comm,mul_left_comm,mul_assoc,apply_ite]

/-- A physical operator acts before any environment is discarded. -/
def acted (V : Matrix (Fin b) (Fin a) ℂ) (P : Matrix (Fin a × Fin e) (Fin c) ℂ) :=
  (V ⊗ₖ (1:Operator e))*P

theorem acted_apply (V : Matrix (Fin b) (Fin a) ℂ) (P : Matrix (Fin a × Fin e) (Fin c) ℂ)
    (i : Fin b) (z : Fin e) (x : Fin c) : acted V P (i,z) x=∑ j,V i j*P (j,z) x := by
  simp [acted,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kroneckerMap_apply,Matrix.one_apply]

def slice (P : Matrix (Fin a × Fin e) (Fin c) ℂ) (z : Fin e) : Matrix (Fin a) (Fin c) ℂ := fun i j => P (i,z) j

theorem acted_map (V : Matrix (Fin b) (Fin a) ℂ) (P : Matrix (Fin a × Fin e) (Fin c) ℂ) :
    dilationMap (acted V P)=(adMap V).comp (dilationMap P) := by
  have hslice (z : Fin e) : slice (acted V P) z=V*slice P z := by
    ext i j
    exact acted_apply V P i z j
  apply LinearMap.ext
  intro X
  simp only [dilationMap,MatrixMap.ofKraus,LinearMap.comp_apply,adMap_apply]
  change (∑ z : Fin e, slice (acted V P) z*X*(slice (acted V P) z)ᴴ) =
    V*(∑ z : Fin e, slice P z*X*(slice P z)ᴴ)*Vᴴ
  simp_rw [hslice,Matrix.conjTranspose_mul]
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]


def environmentEquiv (b d e : ℕ) : Fin (b*d) × Fin e ≃ Fin b × Fin (d*e) :=
  (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _)).trans
    ((Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv))

def regroup (U : Matrix (Fin (b*d) × Fin e) (Fin a) ℂ) :
    Matrix (Fin b × Fin (d*e)) (Fin a) ℂ :=
  Matrix.reindex (environmentEquiv b d e) (Equiv.refl _) U

theorem regroup_apply (U : Matrix (Fin (b*d) × Fin e) (Fin a) ℂ)
    (i : Fin b) (z : Fin d) (v : Fin e) (x : Fin a) :
    regroup U (i,finProdFinEquiv (z,v)) x=U (finProdFinEquiv (i,z),v) x := by
  simp [regroup,environmentEquiv,Matrix.reindex_apply]

theorem regroup_norm (U : Matrix (Fin (b*d) × Fin e) (Fin a) ℂ) : ‖regroup U‖=‖U‖ :=
  TensorPower.norm_reindex _ _ _

theorem regroup_map (U : Matrix (Fin (b*d) × Fin e) (Fin a) ℂ) :
    dilationMap (regroup U)=(discardRight b d).toLinearMap.comp (dilationMap U) := by
  apply LinearMap.ext
  intro X
  ext i j
  change dilationMap (regroup U) X i j=(discardRight b d).apply (dilationMap U X) i j
  rw [BulkMarginal.discardRight_apply_any]
  simp [dilationMap,MatrixMap.ofKraus,Matrix.sum_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,← finProdFinEquiv.sum_comp,Fintype.sum_prod_type,regroup_apply]

def branch (P : Matrix (Fin c × Fin e) (Fin 1) ℂ)
    (J : Matrix (Fin d) (Fin c) ℂ) (V : Matrix (Fin (b*d)) (Fin (a*c)) ℂ) : Matrix (Fin b) (Fin a) ℂ :=
  (preparation b (acted J P))ᴴ * acted V (preparation a P)

theorem acted_norm (V : Matrix (Fin b) (Fin a) ℂ) (P : Matrix (Fin a × Fin e) (Fin c) ℂ) :
    ‖acted V P‖≤‖V‖*‖P‖ :=
  (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (TensorNorm.kronecker_one_opNorm_le V) (norm_nonneg _))

theorem acted_isometry (J : Matrix (Fin d) (Fin c) ℂ) (P : Matrix (Fin c × Fin e) (Fin 1) ℂ)
    (hJ : Jᴴ*J=1) (hP : Pᴴ*P=1) : (acted J P)ᴴ*acted J P=1 := by
  simp only [acted,Matrix.conjTranspose_mul,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  calc
    _ = Pᴴ*((Jᴴ ⊗ₖ (1:Operator e))*(J ⊗ₖ (1:Operator e)))*P := by simp [Matrix.mul_assoc]
    _ = 1 := by rw [← Matrix.mul_kronecker_mul,hJ,Matrix.one_mul,Matrix.one_kronecker_one,Matrix.mul_one,hP]

theorem branch_norm (P : Matrix (Fin c × Fin e) (Fin 1) ℂ) (hP : Pᴴ*P=1)
    (J : Matrix (Fin d) (Fin c) ℂ) (hJ : Jᴴ*J=1)
    (V : Matrix (Fin (b*d)) (Fin (a*c)) ℂ) : ‖branch P J V‖≤‖V‖ := by
  have hA : ‖preparation a P‖≤1 := UniformApproximation.norm_isometry_le_one _ (preparation_isometry P hP)
  have hB : ‖preparation b (acted J P)‖≤1 := UniformApproximation.norm_isometry_le_one _
    (preparation_isometry _ (acted_isometry J P hJ hP))
  calc
    _ ≤ ‖(preparation b (acted J P))ᴴ‖*‖acted V (preparation a P)‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1*(‖V‖*1) := by
      apply mul_le_mul
      · simpa only [Matrix.l2_opNorm_conjTranspose] using hB
      · exact (acted_norm V _).trans (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
      · exact norm_nonneg _
      · norm_num
    _ = _ := by ring


def environmentRow (Q : Matrix (Fin d × Fin e) (Fin 1) ℂ) : Matrix (Fin 1) (Fin (d*e)) ℂ :=
  Matrix.reindex (Equiv.refl _) finProdFinEquiv Qᴴ

theorem environmentRow_norm (Q : Matrix (Fin d × Fin e) (Fin 1) ℂ) : ‖environmentRow Q‖=‖Q‖ := by
  rw [environmentRow,TensorPower.norm_reindex,Matrix.l2_opNorm_conjTranspose]

theorem environment_filter (Q : Matrix (Fin d × Fin e) (Fin 1) ℂ)
    (U : Matrix (Fin (b*d) × Fin e) (Fin a) ℂ) :
    ((1:Operator b) ⊗ₖ environmentRow Q)*regroup U = BranchExtraction.lift ((preparation b Q)ᴴ*U) := by
  ext ⟨i,z⟩ x
  have hz : z=0 := Subsingleton.elim _ _
  subst z
  have hd (u : Fin d) (v : Fin e) : (finProdFinEquiv (u,v)).divNat=u :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (u,v))
  have he (u : Fin d) (v : Fin e) : (finProdFinEquiv (u,v)).modNat=v :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (u,v))
  simp [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kroneckerMap_apply,Matrix.one_apply,hd,he,
    environmentRow,Matrix.reindex_apply,Matrix.conjTranspose_apply,regroup_apply,
    BranchExtraction.lift,← finProdFinEquiv.sum_comp,preparation_apply,apply_ite]

theorem branch_cpLe (P : Matrix (Fin c × Fin e) (Fin 1) ℂ) (hP : Pᴴ*P=1)
    (J : Matrix (Fin d) (Fin c) ℂ) (hJ : Jᴴ*J=1)
    (V : Matrix (Fin (b*d)) (Fin (a*c)) ℂ) :
    MatrixMap.CPLe (adMap (branch P J V))
      ((discardRight b d).toLinearMap.comp ((adMap V).comp (dilationMap (preparation a P)))) := by
  have hQ : ‖environmentRow (acted J P)‖≤1 := by
    rw [environmentRow_norm]
    exact UniformApproximation.norm_isometry_le_one _ (acted_isometry J P hJ hP)
  have h := DominatedSubchannels.dilationMap_environment_cpLe
    (regroup (acted V (preparation a P))) (environmentRow (acted J P)) zero_le_one
    (by nlinarith [norm_nonneg (environmentRow (acted J P))])
  rw [environment_filter,BranchExtraction.dilationMap_lift,regroup_map,acted_map] at h
  simpa only [Complex.ofReal_one,one_smul,branch] using h


theorem preparation_intertwines (P : Matrix (Fin c × Fin e) (Fin 1) ℂ)
    (J : Matrix (Fin d) (Fin c) ℂ) (K : Matrix (Fin b) (Fin a) ℂ) :
    preparation b (acted J P)*K =
      acted (Matrix.reindex finProdFinEquiv finProdFinEquiv (K ⊗ₖ J)) (preparation a P) := by
  ext ⟨i,v⟩ x
  obtain ⟨⟨y,z⟩,rfl⟩ := finProdFinEquiv.surjective i
  have hd (u : Fin a) (v : Fin c) : (finProdFinEquiv (u,v)).divNat=u :=
    congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (u,v))
  have he (u : Fin a) (v : Fin c) : (finProdFinEquiv (u,v)).modNat=v :=
    congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (u,v))
  simp [Matrix.mul_apply,preparation_apply,hd,he,acted_apply,← finProdFinEquiv.sum_comp,
    Fintype.sum_prod_type,Matrix.reindex_apply,Matrix.kroneckerMap_apply,
    Finset.mul_sum,Finset.sum_mul,mul_comm,mul_left_comm,mul_assoc]

/-- Adjoint equality is proved from the actual represented channel, not assumed. -/
theorem compression_eq_heisenberg (U : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (Φ : KrausChannel a b) (hU : dilationMap U=Φ.toLinearMap) (X : Operator b) :
    Uᴴ*(X ⊗ₖ (1:Operator e))*U = heisenbergMap Φ X := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro Y
  rw [heisenbergMap_pairing]
  have hm := congrArg (fun f : MatrixMap a b => f Y) hU
  change dilationMap U Y=Φ.apply Y at hm
  rw [← hm,dilationMap_apply,Matrix.trace_mul_comm (KrausChannel.traceEnvironment _),trace_partialTrace_duality]
  calc
    _ = ((Y*Uᴴ*(X ⊗ₖ (1:Operator e)))*U).trace := by simp [Matrix.mul_assoc]
    _ = (U*(Y*Uᴴ*(X ⊗ₖ (1:Operator e)))).trace := Matrix.trace_mul_comm _ _
    _ = ((U*Y*Uᴴ)*(X ⊗ₖ (1:Operator e))).trace := by simp [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

theorem preparation_eq_append (P : Matrix (Fin c × Fin e) (Fin 1) ℂ)
    (τ : State c) (hτ : dilationMap P 1=τ.matrix) :
    dilationMap (preparation a P)=(appendState a τ).toLinearMap := by
  apply LinearMap.ext
  intro X
  rw [preparation_map,hτ]
  exact (appendState_apply a τ X).symm

/-- Coherent contraction has exactly the desired weighted overlap. -/
theorem branch_overlap (P : Matrix (Fin c × Fin e) (Fin 1) ℂ)
    (τ : State c) (hτ : dilationMap P 1=τ.matrix)
    (J : Matrix (Fin d) (Fin c) ℂ) (K : Matrix (Fin b) (Fin a) ℂ)
    (V : Matrix (Fin (b*d)) (Fin (a*c)) ℂ) :
    Kᴴ*branch P J V = weightedDiscardMap a τ
      ((Matrix.reindex finProdFinEquiv finProdFinEquiv (K ⊗ₖ J))ᴴ*V) := by
  let T := Matrix.reindex finProdFinEquiv finProdFinEquiv (K ⊗ₖ J)
  have h := congrArg Matrix.conjTranspose (preparation_intertwines P J K)
  simp only [Matrix.conjTranspose_mul] at h
  rw [branch,← Matrix.mul_assoc,h]
  change ((T ⊗ₖ (1:Operator e))*preparation a P)ᴴ*acted V (preparation a P) = _
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  have he : (preparation a P)ᴴ*(Tᴴ ⊗ₖ (1:Operator e))*acted V (preparation a P) =
      (preparation a P)ᴴ*((Tᴴ*V) ⊗ₖ (1:Operator e))*preparation a P := by
    dsimp [acted]
    rw [show (Tᴴ*V) ⊗ₖ (1:Operator e)=(Tᴴ ⊗ₖ (1:Operator e))*(V ⊗ₖ (1:Operator e)) by
      rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]]
    simp [Matrix.mul_assoc]
  rw [he]
  exact compression_eq_heisenberg _ _ (preparation_eq_append P τ hτ) _

/-- The canonical preparation vector is normalized and has precisely the supplied state as marginal. -/
theorem replacer_preparation (τ : State c) :
    (ReplacerChannel.channel 1 τ).stinespringᴴ*(ReplacerChannel.channel 1 τ).stinespring=1 ∧
      dilationMap (ReplacerChannel.channel 1 τ).stinespring 1=τ.matrix := by
  refine ⟨(ReplacerChannel.channel 1 τ).stinespring_isometry,?_⟩
  rw [dilationMap_apply,KrausChannel.traceEnvironment_stinespring,ReplacerChannel.channel_apply]
  simp


theorem branch_dominated_marginal (P : Matrix (Fin c × Fin e) (Fin 1) ℂ) (hP : Pᴴ*P=1)
    (τ : State c) (hτ : dilationMap P 1=τ.matrix)
    (J : Matrix (Fin d) (Fin c) ℂ) (hJ : Jᴴ*J=1)
    (V : Matrix (Fin (b*d)) (Fin (a*c)) ℂ)
    (M : KrausChannel (a*c) (b*d)) (p : ℝ) (hp : 0≤p)
    (hdom : MatrixMap.CPLe (Complex.ofReal p•adMap V) M.toLinearMap) :
    MatrixMap.CPLe (Complex.ofReal p•adMap (branch P J V)) (BulkMarginal.pairMarginal τ M).toLinearMap := by
  let Q := (discardRight b d).toLinearMap.comp ((adMap V).comp (appendState a τ).toLinearMap)
  have hB : MatrixMap.CPLe (adMap (branch P J V)) Q := by
    simpa only [preparation_eq_append P τ hτ] using branch_cpLe P hP J hJ V
  have hBs : MatrixMap.CPLe (Complex.ofReal p•adMap (branch P J V)) (Complex.ofReal p•Q) := by
    have h := MatrixMap.completelyPositive_smul hp hB
    simpa only [smul_sub] using h
  apply MatrixMap.cpLe_trans hBs
  have h := LocalReplacement.cp_comp (MatrixMap.completelyPositive_toLinearMap (discardRight b d))
    (LocalReplacement.cp_comp hdom (MatrixMap.completelyPositive_toLinearMap (appendState a τ)))
  change MatrixMap.CompletelyPositive _
  convert h using 1
  apply LinearMap.ext
  intro X
  change (BulkMarginal.pairMarginal τ M).apply X-Complex.ofReal p•Q X =
    (discardRight b d).apply ((M.toLinearMap-Complex.ofReal p•adMap V) ((appendState a τ).apply X))
  simp only [BulkMarginal.pairMarginal,KrausChannel.compose_apply,LinearMap.sub_apply,
    LinearMap.smul_apply]
  change _ = (discardRight b d).toLinearMap (M.apply ((appendState a τ).apply X)-
    Complex.ofReal p•adMap V ((appendState a τ).apply X))
  rw [map_sub,map_smul]
  rfl

/-- A concrete coherent branch for every actual state and dominated channel. -/
theorem exists_branch (τ : State c) (J : Matrix (Fin d) (Fin c) ℂ) (hJ : Jᴴ*J=1)
    (V : Matrix (Fin (b*d)) (Fin (a*c)) ℂ) (M : KrausChannel (a*c) (b*d))
    (p : ℝ) (hp : 0≤p) (hdom : MatrixMap.CPLe (Complex.ofReal p•adMap V) M.toLinearMap) :
    ∃ Z : Matrix (Fin b) (Fin a) ℂ, ‖Z‖≤‖V‖ ∧
      MatrixMap.CPLe (Complex.ofReal p•adMap Z) (BulkMarginal.pairMarginal τ M).toLinearMap ∧
      ∀ K : Matrix (Fin b) (Fin a) ℂ, Kᴴ*Z=weightedDiscardMap a τ
        ((Matrix.reindex finProdFinEquiv finProdFinEquiv (K ⊗ₖ J))ᴴ*V) := by
  let P := (ReplacerChannel.channel 1 τ).stinespring
  obtain ⟨hP,hτ⟩ := replacer_preparation τ
  refine ⟨branch P J V,branch_norm P hP J hJ V,
    branch_dominated_marginal P hP τ hτ J hJ V M p hp hdom,?_⟩
  intro K
  exact branch_overlap P τ hτ J K V

end GeneralizedChannelStein.CoherentMarginal
