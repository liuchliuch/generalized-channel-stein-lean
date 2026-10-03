import GeneralizedChannelStein.LocalReplacement
import GeneralizedChannelStein.RepeatedBlocks
import GeneralizedChannelStein.StatePreserving
import GeneralizedChannelStein.CovariantFamilies

/-! Iterated F5 is literal bulk state insertion and output partial trace. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.BulkMarginal
open QuantumChannelStein Matrix ChannelPowerReindex PerfectDiscrimination RepeatedBlocks
open scoped BigOperators Kronecker ComplexOrder
variable {a b : ℕ}

def joinEquiv (d n r : ℕ) : Fin (d^n)×Fin (d^r) ≃ Fin (d^(n+r)) :=
  finProdFinEquiv.trans (channelAddEquiv d n r)

def join (d n r : ℕ) (i : Fin (d^n)) (j : Fin (d^r)) : Fin (d^(n+r)) := joinEquiv d n r (i,j)

theorem join_val (d n r : ℕ) (i : Fin (d^n)) (j : Fin (d^r)) :
    (join d n r i j).val = j.val+d^r*i.val := by
  simp [join,joinEquiv,channelAddEquiv_eq_cast]

theorem join_assoc (d n r s : ℕ) (i : Fin (d^n)) (j : Fin (d^r)) (z : Fin (d^s)) :
    (join d (n+r) s (join d n r i j) z).val =
      (join d n (r+s) i (join d r s j z)).val := by
  simp only [join_val,Nat.pow_add]
  ring

def appendMatrix (n r : ℕ) (τ : State a) (X : Operator (a^n)) : Operator (a^(n+r)) :=
  Matrix.reindex (joinEquiv a n r) (joinEquiv a n r) (X⊗ₖ(statePower τ r).matrix)

@[simp] theorem appendMatrix_apply (n r : ℕ) (τ : State a) (X : Operator (a^n))
    (i j : Fin (a^n)) (u v : Fin (a^r)) :
    appendMatrix n r τ X (join a n r i u) (join a n r j v) = X i j * (statePower τ r).matrix u v := by
  simp [appendMatrix,join,Matrix.reindex_apply]

def partialOutput (n r : ℕ) (Y : Operator (b^(n+r))) : Operator (b^n) :=
  fun i j => ∑ u : Fin (b^r), Y (join b n r i u) (join b n r j u)

theorem statePower_join (τ : State a) (r s : ℕ) (i j : Fin (a^r)) (u v : Fin (a^s)) :
    (statePower τ (r+s)).matrix (join a r s i u) (join a r s j v) =
      (statePower τ r).matrix i j * (statePower τ s).matrix u v := by
  rw [← statePower_add_matrix τ r s]
  simp [join,joinEquiv,Matrix.reindex_apply]

theorem appendMatrix_succ (n r : ℕ) (τ : State a) (X : Operator (a^n)) :
    appendMatrix (n+r) 1 τ (appendMatrix n r τ X) = appendMatrix n (r+1) τ X := by
  ext i j
  obtain ⟨⟨i,u⟩,rfl⟩ := (joinEquiv a (n+r) 1).surjective i
  obtain ⟨⟨j,v⟩,rfl⟩ := (joinEquiv a (n+r) 1).surjective j
  obtain ⟨⟨i,x⟩,rfl⟩ := (joinEquiv a n r).surjective i
  obtain ⟨⟨j,y⟩,rfl⟩ := (joinEquiv a n r).surjective j
  change appendMatrix (n+r) 1 τ (appendMatrix n r τ X)
    (join a (n+r) 1 (join a n r i x) u) (join a (n+r) 1 (join a n r j y) v) = _
  rw [appendMatrix_apply,appendMatrix_apply]
  have hi : join a (n+r) 1 (join a n r i x) u = join a n (r+1) i (join a r 1 x u) :=
    Fin.ext (join_assoc a n r 1 i x u)
  have hj : join a (n+r) 1 (join a n r j y) v = join a n (r+1) j (join a r 1 y v) :=
    Fin.ext (join_assoc a n r 1 j y v)
  change _ = appendMatrix n (r+1) τ X (join a (n+r) 1 (join a n r i x) u) (join a (n+r) 1 (join a n r j y) v)
  rw [hi,hj,appendMatrix_apply,statePower_join]
  ring

theorem partialOutput_succ (n r : ℕ) (Y : Operator (b^(n+(r+1)))) :
    partialOutput n r (partialOutput (n+r) 1 Y) = partialOutput n (r+1) Y := by
  ext i j
  change (∑ x : Fin (b^r), ∑ z : Fin (b^1),
    Y (join b (n+r) 1 (join b n r i x) z) (join b (n+r) 1 (join b n r j x) z)) = _
  have hi (x : Fin (b^r)) (z : Fin (b^1)) :
      join b (n+r) 1 (join b n r i x) z = join b n (r+1) i (join b r 1 x z) :=
    Fin.ext (join_assoc b n r 1 i x z)
  have hj (x : Fin (b^r)) (z : Fin (b^1)) :
      join b (n+r) 1 (join b n r j x) z = join b n (r+1) j (join b r 1 x z) :=
    Fin.ext (join_assoc b n r 1 j x z)
  simp_rw [hi,hj]
  have h := (joinEquiv b r 1).sum_comp (fun u => Y (join b n (r+1) i u) (join b n (r+1) j u))
  simpa only [Fintype.sum_prod_type,join] using h

theorem join_zero (d n : ℕ) (i : Fin (d^n)) (u : Fin (d^0)) : join d n 0 i u=i := by
  apply Fin.ext
  rw [join_val]
  have hu : u.val=0 := by
    have hu : u.val<1 := by simpa only [pow_zero] using u.isLt
    omega
  simp [hu]

theorem statePower_zero_matrix (τ : State a) : (statePower τ 0).matrix=1 := by
  ext i j
  haveI : Subsingleton (Fin (a^0)) := by simpa only [pow_zero] using (inferInstance : Subsingleton (Fin 1))
  have h : i=j := Subsingleton.elim _ _
  simp [statePower,TensorPower.tensorPower,Matrix.reindex_apply,Matrix.one_apply,h]

theorem appendMatrix_zero (n : ℕ) (τ : State a) (X : Operator (a^n)) : appendMatrix n 0 τ X=X := by
  ext i j
  have h := appendMatrix_apply n 0 τ X i j (0:Fin (a^0)) (0:Fin (a^0))
  simpa only [join_zero,statePower_zero_matrix,Matrix.one_apply_eq,mul_one] using h

theorem partialOutput_zero (n : ℕ) (Y : Operator (b^n)) : partialOutput n 0 Y=Y := by
  ext i j
  simp [partialOutput,join_zero]

/-- The literal insertion/discarding channel for a whole final block. -/
def bulkChannel (n r : ℕ) (τ : State a) (Φ : KrausChannel (a^(n+r)) (b^(n+r))) :
    KrausChannel (a^n) (b^n) :=
  (discardRight (b^n) (b^r)).compose
    ((reindexChannel (channelAddEquiv a n r).symm (channelAddEquiv b n r).symm Φ).compose
      (appendState (a^n) (statePower τ r)))

theorem bulkChannel_apply (n r : ℕ) (τ : State a) (Φ : KrausChannel (a^(n+r)) (b^(n+r)))
    (X : Operator (a^n)) :
    (bulkChannel n r τ Φ).apply X = partialOutput n r (Φ.apply (appendMatrix n r τ X)) := by
  simp only [bulkChannel,KrausChannel.compose_apply,appendState_apply,reindexChannel_apply_any,Equiv.symm_symm]
  have hin : Matrix.reindex (channelAddEquiv a n r) (channelAddEquiv a n r)
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (X⊗ₖ(statePower τ r).matrix)) = appendMatrix n r τ X := by
    ext i j; rfl
  rw [hin]
  have hout (Y : Operator (b^(n+r))) : Matrix.reindex (channelAddEquiv b n r).symm (channelAddEquiv b n r).symm Y =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (fun i j => Y (join b n r i.1 i.2) (join b n r j.1 j.2)) := by
    ext i j
    obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
    simp [join,joinEquiv,Matrix.reindex_apply]
  rw [hout,discardRight_apply]
  rfl

/-- Repeated F5 is exactly the bulk channel, on arbitrary entangled operators. -/
theorem iteratedMarginal_apply (n r : ℕ) (τ : State a) (Φ : KrausChannel (a^(n+r)) (b^(n+r)))
    (X : Operator (a^n)) :
    (iteratedMarginal n τ r Φ).apply X = partialOutput n r (Φ.apply (appendMatrix n r τ X)) := by
  induction r with
  | zero => simp [iteratedMarginal,appendMatrix_zero,partialOutput_zero]
  | succ r ih =>
    change (iteratedMarginal n τ r (marginalChannel (n+r) τ Φ)).apply X = _
    rw [ih]
    change partialOutput n r ((bulkChannel (n+r) 1 τ Φ).apply (appendMatrix n r τ X)) = _
    rw [bulkChannel_apply,appendMatrix_succ,partialOutput_succ]

theorem iteratedMarginal_eq_bulk (n r : ℕ) (τ : State a) (Φ : KrausChannel (a^(n+r)) (b^(n+r))) :
    (iteratedMarginal n τ r Φ).toLinearMap = (bulkChannel n r τ Φ).toLinearMap := by
  ext X i j
  exact congrFun (congrFun ((iteratedMarginal_apply n r τ Φ X).trans (bulkChannel_apply n r τ Φ X).symm) i) j

theorem discardRight_apply_any (c d : ℕ) (Y : Operator (c*d)) :
    (discardRight c d).apply Y = fun i j => ∑ z : Fin d,
      Y (finProdFinEquiv (i,z)) (finProdFinEquiv (j,z)) := by
  have h := discardRight_apply c d (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm Y)
  simpa only [Matrix.reindex_apply,Matrix.submatrix_submatrix,Function.comp_def,
    Equiv.symm_apply_apply,Matrix.submatrix_id_id] using h

def pairMarginal {c d : ℕ} (τ : State c) (Φ : KrausChannel (a*c) (b*d)) : KrausChannel a b :=
  (discardRight b d).compose (Φ.compose (appendState a τ))

theorem pairMarginal_apply {c d : ℕ} (τ : State c) (Φ : KrausChannel (a*c) (b*d)) (X : Operator a) :
    (pairMarginal τ Φ).apply X = fun i j => ∑ z : Fin d,
      Φ.apply (Matrix.reindex finProdFinEquiv finProdFinEquiv (X⊗ₖτ.matrix))
        (finProdFinEquiv (i,z)) (finProdFinEquiv (j,z)) := by
  rw [pairMarginal,KrausChannel.compose_apply,KrausChannel.compose_apply,appendState_apply,discardRight_apply_any]

theorem replaceRight_single {c : ℕ} (τ : Operator c) (i j : Fin a) (u v : Fin c) :
    LocalReplacement.replaceRight a τ (Matrix.single (finProdFinEquiv (i,u)) (finProdFinEquiv (j,v)) 1) =
      if u=v then Matrix.reindex finProdFinEquiv finProdFinEquiv ((Matrix.single i j 1)⊗ₖτ) else 0 := by
  ext x y
  obtain ⟨⟨x1,x2⟩,rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨y1,y2⟩,rfl⟩ := finProdFinEquiv.surjective y
  by_cases h : u=v
  · subst v
    simp [LocalReplacement.replaceRight,Matrix.reindex_apply,Matrix.single,
      finProdFinEquiv.injective.eq_iff,Prod.mk.injEq,ite_and]
  · simp [LocalReplacement.replaceRight,Matrix.reindex_apply,Matrix.single,
      finProdFinEquiv.injective.eq_iff,Prod.mk.injEq,ite_and,h,eq_comm]

/-- Keeping the marginal and independently preparing the replaced outputs is
exactly the two-sided local replacement map, on all operators. -/
theorem tensor_pairMarginal_eq_replaced {c d : ℕ} (τ : State c) (ω : State d)
    (Φ : KrausChannel (a*c) (b*d)) :
    ((pairMarginal τ Φ).tensor (ReplacerChannel.channel c ω)).toLinearMap =
      LocalReplacement.replacedMap Φ.toLinearMap τ.matrix ω.matrix := by
  rw [← MatrixMap.tensor_kraus_toLinearMap]
  apply MatrixMap.choi_injective
  ext ⟨i,x⟩ ⟨j,y⟩
  obtain ⟨⟨i1,i2⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j1,j2⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨x1,x2⟩,rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨y1,y2⟩,rfl⟩ := finProdFinEquiv.surjective y
  change MatrixMap.tensor (pairMarginal τ Φ).toLinearMap (ReplacerChannel.channel c ω).toLinearMap
    (Matrix.single (finProdFinEquiv (i1,i2)) (finProdFinEquiv (j1,j2)) 1)
    (finProdFinEquiv (x1,x2)) (finProdFinEquiv (y1,y2)) = _
  rw [MatrixMap.tensor_single]
  change (Matrix.reindex finProdFinEquiv finProdFinEquiv
    (((pairMarginal τ Φ).apply (Matrix.single i1 j1 1)) ⊗ₖ
      (ReplacerChannel.channel c ω).apply (Matrix.single i2 j2 1))) _ _ = _
  rw [pairMarginal_apply,ReplacerChannel.channel_apply]
  change _ = LocalReplacement.replaceRight b ω.matrix
    (Φ.apply (LocalReplacement.replaceRight a τ.matrix
      (Matrix.single (finProdFinEquiv (i1,i2)) (finProdFinEquiv (j1,j2)) 1))) _ _
  rw [replaceRight_single]
  by_cases h : i2=j2
  · subst j2
    simp [LocalReplacement.replaceRight,Matrix.reindex_apply,Matrix.trace,Matrix.diag,Matrix.single]
  · simp [h,Ne.symm h,LocalReplacement.replaceRight,Matrix.reindex_apply,Matrix.trace,Matrix.diag,Matrix.single,ite_and]

/-- The output-replaced bulk marginal agrees with `replacedMap` in the
canonical power-add coordinates, not merely on product inputs. -/
theorem tensor_iterated_eq_replaced (n r : ℕ) (τ : State a) (ω : State b)
    (Φ : KrausChannel (a^(n+r)) (b^(n+r))) :
    (tensorBlocks n r (iteratedMarginal n τ r Φ)
      (ReplacerChannel.channel (a^r) (statePower ω r))).toLinearMap =
    ChannelTransport.reindexMap (channelAddEquiv a n r) (channelAddEquiv b n r)
      (LocalReplacement.replacedMap
        (reindexChannel (channelAddEquiv a n r).symm (channelAddEquiv b n r).symm Φ).toLinearMap
        (statePower τ r).matrix (statePower ω r).matrix) := by
  rw [tensorBlocks,ChannelTransport.reindexChannel_map]
  congr 1
  rw [← MatrixMap.tensor_kraus_toLinearMap,iteratedMarginal_eq_bulk]
  change MatrixMap.tensor (pairMarginal (statePower τ r)
    (reindexChannel (channelAddEquiv a n r).symm (channelAddEquiv b n r).symm Φ)).toLinearMap _ = _
  rw [MatrixMap.tensor_kraus_toLinearMap,tensor_pairMarginal_eq_replaced]

/-- F5 iterated, followed by F2 and the fixed replacer, supplies precisely
the local replacement channel required in Lemma 28. -/
theorem replacedMap_mem (F : AlternativeFamily a b) (hF : Admissible F)
    (τ : State a) (hτ : QuantitativeAt F τ) (ω : State b)
    (hω : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (n r : ℕ) (hn : 0<n) (hr : 0<r)
    (Φ : KrausChannel (a^(n+r)) (b^(n+r))) (hΦ : Φ.toLinearMap∈F (n+r)) :
    ChannelTransport.reindexMap (channelAddEquiv a n r) (channelAddEquiv b n r)
      (LocalReplacement.replacedMap
        (reindexChannel (channelAddEquiv a n r).symm (channelAddEquiv b n r).symm Φ).toLinearMap
        (statePower τ r).matrix (statePower ω r).matrix) ∈ F (n+r) := by
  rw [← tensor_iterated_eq_replaced]
  apply hF.tensor_closed n r hn hr
  · exact hτ.iterated_marginal_closed n r hn Φ hΦ
  · rw [ReplacerChannel.channel_map,← ReplacerChannel.tensorPower_map]
    exact replacer_power_mem F hF.tensor_closed ω hω r hr

end GeneralizedChannelStein.BulkMarginal
