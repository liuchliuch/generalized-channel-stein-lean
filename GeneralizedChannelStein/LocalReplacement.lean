import GeneralizedChannelStein.BranchExtraction
import GeneralizedChannelStein.DimensionDomination
import GeneralizedChannelStein.QuantitativeFamilies

/-! # Literal local replacement maps and their CP order -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.LocalReplacement
open QuantumChannelStein Matrix ChannelEntropy BranchExtraction
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b c d : ℕ}

/-- Trace-and-prepare without a normalization hypothesis. -/
def prepareMap (a : ℕ) (σ : Operator b) : MatrixMap a b where
  toFun X := X.trace • σ
  map_add' X Y := by simp [Matrix.trace_add,add_smul]
  map_smul' s X := by simp [Matrix.trace_smul,smul_smul]

theorem choi_prepareMap (a : ℕ) (σ : Operator b) :
    MatrixMap.choi (prepareMap a σ)=(1:Operator a) ⊗ₖ σ := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [prepareMap,MatrixMap.choi,Matrix.trace,Matrix.diag,Matrix.single,Matrix.one_apply,ite_and,eq_comm]

theorem prepareMap_cp (a : ℕ) (σ : Operator b) (hσ : σ.PosSemidef) :
    MatrixMap.CompletelyPositive (prepareMap a σ) := by
  rw [MatrixMap.completelyPositive_iff_choi_positive,choi_prepareMap]
  exact MatrixMap.posSemidef_kronecker Matrix.PosSemidef.one hσ

theorem prepareMap_channel (a : ℕ) (σ : State b) :
    prepareMap a σ.matrix=(ReplacerChannel.channel a σ).toLinearMap :=
  (ReplacerChannel.channel_map a σ).symm

theorem prepareMap_mono (a : ℕ) (σ τ : Operator b) (h : (τ-σ).PosSemidef) :
    MatrixMap.CPLe (prepareMap a σ) (prepareMap a τ) := by
  have hh := prepareMap_cp a (τ-σ) h
  change MatrixMap.CompletelyPositive _
  convert hh using 1
  ext X i j
  simp [prepareMap,smul_sub]

theorem cp_comp {P : MatrixMap b c} {Q : MatrixMap a b}
    (hP : MatrixMap.CompletelyPositive P) (hQ : MatrixMap.CompletelyPositive Q) :
    MatrixMap.CompletelyPositive (P.comp Q) := by
  intro r X hX
  have h := hP r _ (hQ r X hX)
  convert h using 1

theorem cpLe_comp {P P' : MatrixMap b c} {Q Q' : MatrixMap a b}
    (hP' : MatrixMap.CompletelyPositive P') (hQ : MatrixMap.CompletelyPositive Q)
    (hP : MatrixMap.CPLe P P') (hQ' : MatrixMap.CPLe Q Q') :
    MatrixMap.CPLe (P.comp Q) (P'.comp Q') := by
  have h := MatrixMap.completelyPositive_add (cp_comp hP' hQ') (cp_comp hP hQ)
  change MatrixMap.CompletelyPositive _
  convert h using 1
  ext X i j
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.comp_apply,map_sub,Matrix.sub_apply,Matrix.add_apply]
  ring

/-- Replace the right factor, keeping the left factor exactly unchanged. -/
def replaceRight (a : ℕ) (σ : Operator b) : MatrixMap (a*b) (a*b) where
  toFun X := Matrix.reindex finProdFinEquiv finProdFinEquiv
    ((fun i j => ∑ z : Fin b, X (finProdFinEquiv (i,z)) (finProdFinEquiv (j,z))) ⊗ₖ σ)
  map_add' X Y := by ext i j; simp [Matrix.reindex_apply,Matrix.kroneckerMap_apply,Finset.sum_add_distrib,add_mul]
  map_smul' s X := by ext i j; simp [Matrix.reindex_apply,Matrix.kroneckerMap_apply,← Finset.mul_sum,mul_assoc]

theorem replaceRight_tensor (a : ℕ) (σ : Operator b) :
    replaceRight a σ=MatrixMap.tensor (KrausChannel.identity a).toLinearMap (prepareMap b σ) := by
  apply MatrixMap.choi_injective
  ext ⟨i,u⟩ ⟨j,v⟩
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨u1,u2⟩,rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨v1,v2⟩,rfl⟩ := finProdFinEquiv.surjective v
  change replaceRight a σ (Matrix.single (finProdFinEquiv (i1,i2)) (finProdFinEquiv (j1,j2)) 1)
    (finProdFinEquiv (u1,u2)) (finProdFinEquiv (v1,v2)) =
    MatrixMap.tensor (KrausChannel.identity a).toLinearMap (prepareMap b σ)
    (Matrix.single (finProdFinEquiv (i1,i2)) (finProdFinEquiv (j1,j2)) 1)
    (finProdFinEquiv (u1,u2)) (finProdFinEquiv (v1,v2))
  rw [MatrixMap.tensor_single]
  simp [replaceRight,prepareMap,Matrix.reindex_apply,Matrix.kroneckerMap_apply,
    KrausChannel.toLinearMap,KrausChannel.identity_apply,Matrix.single,Matrix.trace,Matrix.diag,
    finProdFinEquiv.injective.eq_iff,Prod.mk.injEq,ite_and]
  split_ifs <;> simp_all [Matrix.reindex_apply,Matrix.kroneckerMap_apply,Matrix.single,ite_and]

theorem replaceRight_cp (a : ℕ) (σ : Operator b) (hσ : σ.PosSemidef) :
    MatrixMap.CompletelyPositive (replaceRight a σ) := by
  rw [replaceRight_tensor]
  exact MatrixMap.completelyPositive_tensor (MatrixMap.completelyPositive_toLinearMap _)
    (prepareMap_cp _ _ hσ)

theorem replaceRight_channel (a : ℕ) (σ : State b) :
    replaceRight a σ.matrix=((KrausChannel.identity a).tensor (ReplacerChannel.channel b σ)).toLinearMap := by
  rw [replaceRight_tensor,prepareMap_channel,MatrixMap.tensor_kraus_toLinearMap]

theorem replaceRight_mono (a : ℕ) (σ τ : Operator b) (hσ : σ.PosSemidef) (hτ : τ.PosSemidef)
    (h : (τ-σ).PosSemidef) : MatrixMap.CPLe (replaceRight a σ) (replaceRight a τ) := by
  rw [replaceRight_tensor,replaceRight_tensor]
  exact MatrixMap.cpLe_tensor (MatrixMap.completelyPositive_toLinearMap _)
    (prepareMap_cp _ _ hτ) (MatrixMap.cpLe_refl _) (prepareMap_mono _ _ _ h)

@[simp] theorem replaceRight_smul (a : ℕ) (σ : Operator b) (s : ℝ) :
    replaceRight a (s • σ)=(s:ℂ) • replaceRight a σ := by
  ext X i j
  simp [replaceRight,Matrix.reindex_apply,Matrix.kroneckerMap_apply,Complex.real_smul,mul_comm,mul_left_comm,mul_assoc]

/-- Replace both input and output factors; this is the concrete map used in28. -/
def replacedMap (M : MatrixMap (a*b) (c*d)) (τ : Operator b) (ω : Operator d) : MatrixMap (a*b) (c*d) :=
  (replaceRight c ω).comp (M.comp (replaceRight a τ))

theorem replacedMap_mono (M : MatrixMap (a*b) (c*d)) (hM : MatrixMap.CompletelyPositive M)
    (τ τ' : Operator b) (ω ω' : Operator d)
    (hτ : τ.PosSemidef) (hτ' : τ'.PosSemidef) (hω : ω.PosSemidef) (hω' : ω'.PosSemidef)
    (ht : (τ'-τ).PosSemidef) (hw : (ω'-ω).PosSemidef) :
    MatrixMap.CPLe (replacedMap M τ ω) (replacedMap M τ' ω') := by
  exact cpLe_comp (replaceRight_cp _ _ hω') (cp_comp hM (replaceRight_cp _ _ hτ))
    (replaceRight_mono _ _ _ hω hω' hw)
    (cpLe_comp hM (replaceRight_cp _ _ hτ) (MatrixMap.cpLe_refl _) (replaceRight_mono _ _ _ hτ hτ' ht))

theorem replacedMap_smul_states (M : MatrixMap (a*b) (c*d))
    (τ : Operator b) (ω : Operator d) (t w : ℝ) :
    replacedMap M (t • τ) (w • ω)=Complex.ofReal (t*w) • replacedMap M τ ω := by
  rw [replacedMap,replaceRight_smul,replaceRight_smul]
  ext X i j
  simp [replacedMap,LinearMap.comp_apply,Complex.ofReal_mul,mul_comm,mul_left_comm,mul_assoc]

theorem replacedMap_lower (M : MatrixMap (a*b) (c*d)) (hM : MatrixMap.CompletelyPositive M)
    (τ : Operator b) (ω : Operator d) (hτ : τ.PosSemidef) (hω : ω.PosSemidef)
    (t w : ℝ) (ht : 0≤t) (hw : 0≤w)
    (htτ : (τ-t • (1:Operator b)).PosSemidef) (hwω : (ω-w • (1:Operator d)).PosSemidef) :
    MatrixMap.CPLe (Complex.ofReal (t*w) • replacedMap M 1 1) (replacedMap M τ ω) := by
  rw [← replacedMap_smul_states]
  exact replacedMap_mono M hM _ τ _ ω (Matrix.PosSemidef.one.smul ht) hτ
    (Matrix.PosSemidef.one.smul hw) hω htτ hwω

/-- Replacement respects domination of the original branch. -/
theorem replacedMap_cpLe {P M : MatrixMap (a*b) (c*d)}
    (h : MatrixMap.CPLe P M) (τ : Operator b) (ω : Operator d)
    (hτ : τ.PosSemidef) (hω : ω.PosSemidef) :
    MatrixMap.CPLe (replacedMap P τ ω) (replacedMap M τ ω) := by
  have h₁ := cp_comp h (replaceRight_cp a τ hτ)
  have h₂ := cp_comp (replaceRight_cp c ω hω) h₁
  change MatrixMap.CompletelyPositive _
  convert h₂ using 1
  ext X i j
  simp [replacedMap,LinearMap.comp_apply,map_sub]

@[simp] theorem replacedMap_smul (P : MatrixMap (a*b) (c*d)) (τ : Operator b) (ω : Operator d) (p : ℝ) :
    replacedMap (Complex.ofReal p • P) τ ω=Complex.ofReal p • replacedMap P τ ω := by
  ext X i j
  simp [replacedMap,LinearMap.comp_apply]

/-- Actual normalized channel implementing the two local replacements. -/
def replacedChannel (M : KrausChannel (a*b) (c*d)) (τ : State b) (ω : State d) :
    KrausChannel (a*b) (c*d) :=
  ((KrausChannel.identity c).tensor (ReplacerChannel.channel d ω)).compose
    (M.compose ((KrausChannel.identity a).tensor (ReplacerChannel.channel b τ)))

theorem replacedChannel_map (M : KrausChannel (a*b) (c*d)) (τ : State b) (ω : State d) :
    (replacedChannel M τ ω).toLinearMap=replacedMap M.toLinearMap τ.matrix ω.matrix := by
  rw [replacedMap,replaceRight_channel,replaceRight_channel]
  ext X i j
  change (replacedChannel M τ ω).apply X i j =
    ((KrausChannel.identity c).tensor (ReplacerChannel.channel d ω)).apply
      (M.apply (((KrausChannel.identity a).tensor (ReplacerChannel.channel b τ)).apply X)) i j
  rw [replacedChannel,KrausChannel.compose_apply,KrausChannel.compose_apply]

theorem replaceRight_scalar (a : ℕ) : replaceRight a (1:Operator 1)=LinearMap.id := by
  ext X i j
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  have hi : i2=0 := Subsingleton.elim _ _
  have hj : j2=0 := Subsingleton.elim _ _
  subst i2
  subst j2
  simp [replaceRight,Matrix.reindex_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]

theorem replacedMap_scalar (M : MatrixMap (a*1) (c*1)) : replacedMap M (1:Operator 1) (1:Operator 1)=M := by
  rw [replacedMap,replaceRight_scalar,replaceRight_scalar]
  rfl

end GeneralizedChannelStein.LocalReplacement
