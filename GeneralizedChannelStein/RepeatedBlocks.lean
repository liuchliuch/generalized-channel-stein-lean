import GeneralizedChannelStein.ChannelTransport
import QuantumChannelStein.ChannelDilationPower

/-! # Exact coordinate bookkeeping for free repeated blocks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.RepeatedBlocks
open QuantumChannelStein Matrix TensorPower ChannelPowerReindex ChannelTransport
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

/-- The recursive channel index is the usual base-d positional encoding. -/
theorem channelIndexEquiv_val (d k : ℕ) (i : Index (Fin d) k) :
    (channelIndexEquiv d k i).val =
      ∑ l : Fin k, (indexEquiv (Fin d) k i l).val * d ^ (k - 1 - l.val) := by
  induction k with
  | zero => simp [channelIndexEquiv, Index]
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    simp only [indexEquiv_succ_zero, indexEquiv_succ_succ, Fin.val_zero, Fin.val_succ,
      Nat.add_sub_cancel, Nat.sub_zero]
    change (channelIndexEquiv d k i.2).val + d ^ k * i.1.val = _
    rw [ih]
    have heq (l : Fin k) : k - (l.val + 1) = k - 1 - l.val := by omega
    simp_rw [heq]
    ring

/-- The concatenation equivalence is exactly the ordinary finite index cast. -/
theorem channelAddEquiv_eq_cast (d k l : ℕ) :
    channelAddEquiv d k l = finCongr (Nat.pow_add d k l).symm := by
  ext x
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨i,rfl⟩ := (channelIndexEquiv d k).surjective i
  obtain ⟨j,rfl⟩ := (channelIndexEquiv d l).surjective j
  simp only [channelAddEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    channelConcatEquiv_apply, finCongr_apply]
  change (channelIndexEquiv d (k+l) (indexAddEquiv (Fin d) k l (i,j))).val =
    (channelIndexEquiv d l j).val + d^l * (channelIndexEquiv d k i).val
  rw [channelIndexEquiv_val, Fin.sum_univ_add, channelIndexEquiv_val, channelIndexEquiv_val]
  simp only [indexEquiv_indexAddEquiv_left, indexEquiv_indexAddEquiv_right,
    Fin.val_castAdd, Fin.val_natAdd]
  have hleft (x : Fin k) : k+l-1-x.val = (k-1-x.val)+l := by omega
  have hright (x : Fin l) : k+l-1-(k+x.val) = l-1-x.val := by omega
  simp_rw [hleft,hright,Nat.pow_add]
  rw [Finset.mul_sum, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    ring

theorem reindexChannel_finCongr {a b a' b' : ℕ} (P : KrausChannel a b)
    (ha : a = a') (hb : b = b') :
    reindexChannel (finCongr ha) (finCongr hb) P = P.cast ha hb := by
  cases ha
  cases hb
  rfl

theorem tensor_cast_right {a b c d c' d' : ℕ} (P : KrausChannel a b) (Q : KrausChannel c d)
    (hc : c = c') (hd : d = d') :
    P.tensor (Q.cast hc hd) = (P.tensor Q).cast (congrArg (a * ·) hc) (congrArg (b * ·) hd) := by
  cases hc
  cases hd
  rfl

/-- Repeated k-block channels on the actual km-use coordinate spaces. -/
def repeatBlock {a b : ℕ} (k m : ℕ) (M : KrausChannel (a^k) (b^k)) :
    KrausChannel (a^(k*m)) (b^(k*m)) :=
  (M.tensorPower m).cast (Nat.pow_mul a k m).symm (Nat.pow_mul b k m).symm

theorem repeatBlock_succ {a b : ℕ} (k m : ℕ) (M : KrausChannel (a^k) (b^k)) :
    repeatBlock k (m+1) M =
      (tensorBlocks k (k*m) M (repeatBlock k m M)).cast
        (congrArg (a^·) (by ring : k+k*m=k*(m+1)))
        (congrArg (b^·) (by ring : k+k*m=k*(m+1))) := by
  simp only [repeatBlock, KrausChannel.tensorPower, tensorBlocks,
    channelAddEquiv_eq_cast, reindexChannel_finCongr, tensor_cast_right, KrausChannel.cast_cast]

theorem repeatBlock_one_map {a b : ℕ} (k : ℕ) (M : KrausChannel (a^k) (b^k)) :
    ((repeatBlock k 1 M).cast (by simp) (by simp)).toLinearMap = M.toLinearMap := by
  simpa only [repeatBlock, KrausChannel.cast_cast] using M.tensorPower_one_toLinearMap

theorem cast_mem_family {a b n m : ℕ} (F : AlternativeFamily a b)
    (h : n = m) (P : KrausChannel (a^n) (b^n)) :
    (P.cast (congrArg (a^·) h) (congrArg (b^·) h)).toLinearMap ∈ F m ↔ P.toLinearMap ∈ F n := by
  cases h
  rfl

/-- Tensor closure alone puts every positive number of repeated blocks in F. -/
theorem repeatBlock_mem {a b : ℕ} (F : AlternativeFamily a b)
    (hF : ∀ n m, 0 < n → 0 < m →
      ∀ (P : KrausChannel (a^n) (b^n)) (Q : KrausChannel (a^m) (b^m)),
      P.toLinearMap ∈ F n → Q.toLinearMap ∈ F m →
      (tensorBlocks n m P Q).toLinearMap ∈ F (n+m))
    (k : ℕ) (hk : 0 < k) (M : KrausChannel (a^k) (b^k)) (hM : M.toLinearMap ∈ F k) :
    ∀ m, 0 < m → (repeatBlock k m M).toLinearMap ∈ F (k*m) := by
  intro m hm
  induction m using Nat.case_strong_induction_on with
  | hz => omega
  | hi m ih =>
    by_cases hm0 : m = 0
    · subst m
      have h := repeatBlock_one_map k M
      apply (cast_mem_family F (Nat.mul_one k) (repeatBlock k 1 M)).mp
      rw [h]
      exact hM
    · have hmp : 0 < m := Nat.pos_of_ne_zero hm0
      have h := hF k (k*m) hk (Nat.mul_pos hk hmp) M (repeatBlock k m M) hM
        (ih m (Nat.le_refl m) hmp)
      rw [repeatBlock_succ]
      apply (cast_mem_family F (by ring : k+k*m=k*(m+1)) _).mpr
      exact h

theorem tensor_map_congr {a b c d : ℕ} (P P' : KrausChannel a b) (Q Q' : KrausChannel c d)
    (hP : P.toLinearMap = P'.toLinearMap) (hQ : Q.toLinearMap = Q'.toLinearMap) :
    (P.tensor Q).toLinearMap = (P'.tensor Q').toLinearMap := by
  rw [← MatrixMap.tensor_kraus_toLinearMap, ← MatrixMap.tensor_kraus_toLinearMap, hP, hQ]

theorem cast_map_congr {a b a' b' : ℕ} (P Q : KrausChannel a b)
    (h : P.toLinearMap = Q.toLinearMap) (ha : a = a') (hb : b = b') :
    (P.cast ha hb).toLinearMap = (Q.cast ha hb).toLinearMap := by
  cases ha
  cases hb
  exact h

theorem tensorBlocks_map_congr {a b : ℕ} (k l : ℕ)
    (P P' : KrausChannel (a^k) (b^k)) (Q Q' : KrausChannel (a^l) (b^l))
    (hP : P.toLinearMap = P'.toLinearMap) (hQ : Q.toLinearMap = Q'.toLinearMap) :
    (tensorBlocks k l P Q).toLinearMap = (tensorBlocks k l P' Q').toLinearMap := by
  simp only [tensorBlocks, reindexChannel_map]
  rw [tensor_map_congr P P' Q Q' hP hQ]

theorem tensorPower_cast {a b : ℕ} (N : KrausChannel a b) {n m : ℕ} (h : n = m) :
    (N.tensorPower n).cast (congrArg (a^·) h) (congrArg (b^·) h) = N.tensorPower m := by
  cases h
  rfl

/-- Repeating the true k-use target is exactly the km-use target in these
same coordinates; no free-family relabeling invariance is used. -/
theorem repeatBlock_target_map {a b : ℕ} (N : KrausChannel a b) (k m : ℕ) :
    (repeatBlock k m (N.tensorPower k)).toLinearMap = (N.tensorPower (k*m)).toLinearMap := by
  induction m with
  | zero => simp [repeatBlock, KrausChannel.tensorPower, KrausChannel.cast]
  | succ m ih =>
    rw [repeatBlock_succ]
    have ht := tensorBlocks_map_congr k (k*m) (N.tensorPower k) (N.tensorPower k)
      (repeatBlock k m (N.tensorPower k)) (N.tensorPower (k*m)) rfl ih
    have hp : (tensorBlocks k (k*m) (N.tensorPower k) (N.tensorPower (k*m))).toLinearMap =
        (N.tensorPower (k+k*m)).toLinearMap := tensorPower_add_toLinearMap N k (k*m)
    have h := cast_map_congr _ _ (ht.trans hp)
      (congrArg (a^·) (by ring : k+k*m=k*(m+1)))
      (congrArg (b^·) (by ring : k+k*m=k*(m+1)))
    have he := tensorPower_cast N (by ring : k+k*m=k*(m+1))
    rw [he] at h
    exact h

/-- Empty exact padding changes no channel action. -/
theorem tensorBlocks_zero_map {a b : ℕ} (p : ℕ) (P : KrausChannel (a^p) (b^p)) :
    ((tensorBlocks p 0 P (KrausChannel.identity 1)).cast (by simp) (by simp)).toLinearMap =
      P.toLinearMap := by
  simp only [tensorBlocks, channelAddEquiv_eq_cast, reindexChannel_finCongr, KrausChannel.cast_cast]
  ext X i j
  exact congrFun (congrFun (P.tensor_identity_cast_apply X) i) j

/-- Exact replacer padding requires no F₀ assumption. -/
theorem paddedBlock_mem {a b : ℕ} (F : AlternativeFamily a b)
    (hF : ∀ n m, 0 < n → 0 < m →
      ∀ (P : KrausChannel (a^n) (b^n)) (Q : KrausChannel (a^m) (b^m)),
      P.toLinearMap ∈ F n → Q.toLinearMap ∈ F m →
      (tensorBlocks n m P Q).toLinearMap ∈ F (n+m))
    (ω : State b)
    (hR : ∀ l, 0 < l → ((ReplacerChannel.channel a ω).tensorPower l).toLinearMap ∈ F l)
    (p : ℕ) (hp : 0 < p) (M : KrausChannel (a^p) (b^p)) (hM : M.toLinearMap ∈ F p) (l : ℕ) :
    (tensorBlocks p l M ((ReplacerChannel.channel a ω).tensorPower l)).toLinearMap ∈ F (p+l) := by
  by_cases hl : l = 0
  · subst l
    apply (cast_mem_family F (Nat.add_zero p) _).mp
    rw [show (ReplacerChannel.channel a ω).tensorPower 0 = KrausChannel.identity 1 from rfl,
      tensorBlocks_zero_map]
    exact hM
  · exact hF p l hp (Nat.pos_of_ne_zero hl) M _ hM (hR l (Nat.pos_of_ne_zero hl))

end GeneralizedChannelStein.RepeatedBlocks
