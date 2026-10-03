import QuantumChannelStein.TensorUnit
import QuantumChannelStein.TensorPower

/-! # Concrete channel-power splitting by canonical coordinate permutations -/
noncomputable section
namespace QuantumChannelStein.ChannelPowerReindex
open scoped BigOperators Kronecker
open Matrix
open TensorPower

variable {n m n' m' : ℕ}

/-- Reindex the actual Kraus operators without changing their slots. -/
def reindexChannel (en : Fin n ≃ Fin n') (em : Fin m ≃ Fin m')
    (Φ : KrausChannel n m) : KrausChannel n' m' where
  rank := Φ.rank
  kraus s := Matrix.reindex em en (Φ.kraus s)
  normalized := by
    simp only [Matrix.conjTranspose_reindex]
    change (∑ s, Matrix.reindexLinearEquiv ℂ ℂ en em (Φ.kraus s)ᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ em en (Φ.kraus s)) = 1
    simp_rw [Matrix.reindexLinearEquiv_mul]
    rw [← map_sum, Φ.normalized]
    exact Matrix.reindexLinearEquiv_one ℂ ℂ en

/-- Reindexed channels act by the corresponding input/output conjugations. -/
theorem reindexChannel_apply (en : Fin n ≃ Fin n') (em : Fin m ≃ Fin m')
    (Φ : KrausChannel n m) (X : Operator n) :
    (reindexChannel en em Φ).apply (Matrix.reindex en en X) =
      Matrix.reindex em em (Φ.apply X) := by
  unfold KrausChannel.apply reindexChannel
  simp only [Matrix.conjTranspose_reindex]
  change (∑ s, Matrix.reindexLinearEquiv ℂ ℂ em en (Φ.kraus s) *
    Matrix.reindexLinearEquiv ℂ ℂ en en X *
    Matrix.reindexLinearEquiv ℂ ℂ en em (Φ.kraus s)ᴴ) = _
  simp_rw [Matrix.reindexLinearEquiv_mul]
  rw [← map_sum]
  rfl

/-- Coordinate relabeling commutes with the individual matrix units. -/
theorem reindex_single (en : Fin n ≃ Fin n') (i j : Fin n) :
    Matrix.reindex en en (Matrix.single i j (1 : ℂ)) = Matrix.single (en i) (en j) 1 := by
  ext a b
  simp [Matrix.reindex_apply, Matrix.single, ← Equiv.eq_symm_apply]

/-- The Choi operator changes by precisely the joint input/output permutation. -/
theorem reindexChannel_choi (en : Fin n ≃ Fin n') (em : Fin m ≃ Fin m')
    (Φ : KrausChannel n m) :
    (reindexChannel en em Φ).choi =
      Matrix.reindex (Equiv.prodCongr en em) (Equiv.prodCongr en em) Φ.choi := by
  ext ⟨i, a⟩ ⟨j, b⟩
  obtain ⟨i, rfl⟩ := en.surjective i
  obtain ⟨j, rfl⟩ := en.surjective j
  obtain ⟨a, rfl⟩ := em.surjective a
  obtain ⟨b, rfl⟩ := em.surjective b
  have h := reindexChannel_apply en em Φ (Matrix.single i j 1)
  rw [reindex_single] at h
  have hh := congrFun (congrFun h (em a)) (em b)
  simpa [KrausChannel.choi, Matrix.reindex_apply, Equiv.prodCongr_apply] using hh

/-- The repeated-channel indexing used by the recursive Kraus construction. -/
def channelIndexEquiv (d : ℕ) : (k : ℕ) → Index (Fin d) k ≃ Fin (d ^ k)
  | 0 => by simpa only [pow_zero] using (Equiv.ofUnique (Index (Fin d) 0) (Fin 1))
  | k + 1 => (Equiv.prodCongr (Equiv.refl (Fin d)) (channelIndexEquiv d k)).trans
      (finProdFinEquiv.trans (finCongr (by rw [Nat.pow_succ'])))

/-- Choi entries are unaffected by dimension-equality transports. -/
theorem choi_cast_apply (Φ : KrausChannel n m) (hn : n = n') (hm : m = m')
    (i j : Fin n) (a b : Fin m) :
    (Φ.cast hn hm).choi ((finCongr hn) i, (finCongr hm) a)
      ((finCongr hn) j, (finCongr hm) b) = Φ.choi (i, a) (j, b) := by
  cases hn
  cases hm
  rfl

/-- Tensor-channel Choi entries factor into the two one-channel entries. -/
theorem choi_tensor_apply {r s : ℕ} (Φ : KrausChannel n m) (Ψ : KrausChannel r s)
    (i j : Fin n) (a b : Fin m) (u v : Fin r) (c d : Fin s) :
    (KrausChannel.tensor Φ Ψ).choi
      (finProdFinEquiv (i, u), finProdFinEquiv (a, c))
      (finProdFinEquiv (j, v), finProdFinEquiv (b, d)) =
      Φ.choi (i, a) (j, b) * Ψ.choi (u, c) (v, d) := by
  change MatrixMap.choi (KrausChannel.tensor Φ Ψ).toLinearMap _ _ = _
  rw [← MatrixMap.tensor_kraus_toLinearMap, MatrixMap.choi_tensor]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, MatrixMap.choiShuffle_symm_apply,
    Matrix.kronecker_apply, MatrixMap.choi_toLinearMap]

/-- The genuine repeated-channel Choi entries are products of one-use Choi
entries, in the recursively specified channel coordinates. -/
theorem choi_tensorPower_apply (Φ : KrausChannel n m) (k : ℕ)
    (i j : Index (Fin n) k) (a b : Index (Fin m) k) :
    (KrausChannel.tensorPower Φ k).choi
      (channelIndexEquiv n k i, channelIndexEquiv m k a)
      (channelIndexEquiv n k j, channelIndexEquiv m k b) =
      ∏ l : Fin k, Φ.choi
        (indexEquiv (Fin n) k i l, indexEquiv (Fin m) k a l)
        (indexEquiv (Fin n) k j l, indexEquiv (Fin m) k b l) := by
  induction k with
  | zero =>
    simp [KrausChannel.tensorPower, KrausChannel.choi, KrausChannel.identity_apply,
      Matrix.single]
    constructor <;> exact @Subsingleton.elim (Fin 1) _ _ _
  | succ k ih =>
    have hn : n * n ^ k = n ^ (k + 1) := by rw [Nat.pow_succ']
    have hm : m * m ^ k = m ^ (k + 1) := by rw [Nat.pow_succ']
    change ((KrausChannel.tensor Φ (KrausChannel.tensorPower Φ k)).cast
      hn hm).choi
      ((finCongr hn) (finProdFinEquiv (i.1, channelIndexEquiv n k i.2)),
        (finCongr hm) (finProdFinEquiv (a.1, channelIndexEquiv m k a.2)))
      ((finCongr hn) (finProdFinEquiv (j.1, channelIndexEquiv n k j.2)),
        (finCongr hm) (finProdFinEquiv (b.1, channelIndexEquiv m k b.2))) = _
    rw [choi_cast_apply, choi_tensor_apply, ih, Fin.prod_univ_succ]
    simp only [indexEquiv_succ_zero, indexEquiv_succ_succ]

end QuantumChannelStein.ChannelPowerReindex

noncomputable section
namespace QuantumChannelStein.ChannelPowerReindex
open scoped BigOperators Kronecker
open Matrix TensorPower
variable {n m : ℕ}

/-- Concatenate the channel coordinates of two consecutive independent blocks. -/
def channelConcatEquiv (d k l : ℕ) : Fin (d ^ k) × Fin (d ^ l) ≃ Fin (d ^ (k + l)) :=
  (Equiv.prodCongr (channelIndexEquiv d k).symm (channelIndexEquiv d l).symm).trans
    ((indexAddEquiv (Fin d) k l).trans (channelIndexEquiv d (k + l)))

@[simp] theorem channelConcatEquiv_apply (d k l : ℕ)
    (i : Index (Fin d) k) (j : Index (Fin d) l) :
    channelConcatEquiv d k l (channelIndexEquiv d k i, channelIndexEquiv d l j) =
      channelIndexEquiv d (k + l) (indexAddEquiv (Fin d) k l (i, j)) := by
  simp [channelConcatEquiv, Equiv.prodCongr_apply]

/-- Coordinate permutation from the product of two power channels to the
single power at the sum blocklength. -/
def channelAddEquiv (d k l : ℕ) : Fin (d ^ k * d ^ l) ≃ Fin (d ^ (k + l)) :=
  finProdFinEquiv.symm.trans (channelConcatEquiv d k l)

@[simp] theorem channelAddEquiv_symm_concat (d k l : ℕ)
    (i : Fin (d ^ k)) (j : Fin (d ^ l)) :
    (channelAddEquiv d k l).symm (channelConcatEquiv d k l (i, j)) =
      finProdFinEquiv (i, j) := by
  simp [channelAddEquiv]

/-- Choi entries split at any block boundary in the actual channel powers. -/
theorem choi_tensorPower_add_entry (Φ : KrausChannel n m) (k l : ℕ)
    (i j : Fin (n ^ k)) (u v : Fin (n ^ l))
    (a b : Fin (m ^ k)) (c d : Fin (m ^ l)) :
    (KrausChannel.tensorPower Φ (k + l)).choi
      (channelConcatEquiv n k l (i, u), channelConcatEquiv m k l (a, c))
      (channelConcatEquiv n k l (j, v), channelConcatEquiv m k l (b, d)) =
      (KrausChannel.tensorPower Φ k).choi (i, a) (j, b) *
        (KrausChannel.tensorPower Φ l).choi (u, c) (v, d) := by
  obtain ⟨i, rfl⟩ := (channelIndexEquiv n k).surjective i
  obtain ⟨j, rfl⟩ := (channelIndexEquiv n k).surjective j
  obtain ⟨u, rfl⟩ := (channelIndexEquiv n l).surjective u
  obtain ⟨v, rfl⟩ := (channelIndexEquiv n l).surjective v
  obtain ⟨a, rfl⟩ := (channelIndexEquiv m k).surjective a
  obtain ⟨b, rfl⟩ := (channelIndexEquiv m k).surjective b
  obtain ⟨c, rfl⟩ := (channelIndexEquiv m l).surjective c
  obtain ⟨d, rfl⟩ := (channelIndexEquiv m l).surjective d
  simp only [channelConcatEquiv_apply, choi_tensorPower_apply, Fin.prod_univ_add,
    indexEquiv_indexAddEquiv_left, indexEquiv_indexAddEquiv_right]

/-- Explicit Choi equality for splitting an actual repeated-use channel. -/
theorem tensorPower_add_choi (Φ : KrausChannel n m) (k l : ℕ) :
    (reindexChannel (channelAddEquiv n k l) (channelAddEquiv m k l)
      (KrausChannel.tensor (KrausChannel.tensorPower Φ k) (KrausChannel.tensorPower Φ l))).choi =
      (KrausChannel.tensorPower Φ (k + l)).choi := by
  rw [reindexChannel_choi]
  ext ⟨i, a⟩ ⟨j, b⟩
  obtain ⟨⟨i, u⟩, rfl⟩ := (channelConcatEquiv n k l).surjective i
  obtain ⟨⟨j, v⟩, rfl⟩ := (channelConcatEquiv n k l).surjective j
  obtain ⟨⟨a, c⟩, rfl⟩ := (channelConcatEquiv m k l).surjective a
  obtain ⟨⟨b, d⟩, rfl⟩ := (channelConcatEquiv m k l).surjective b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_apply, channelAddEquiv_symm_concat,
    choi_tensor_apply, choi_tensorPower_add_entry]

/-- The genuine tensor-power channel splits into its independent blocks up
to the same explicit input/output coordinate permutations for every channel. -/
theorem tensorPower_add_toLinearMap (Φ : KrausChannel n m) (k l : ℕ) :
    (reindexChannel (channelAddEquiv n k l) (channelAddEquiv m k l)
      (KrausChannel.tensor (KrausChannel.tensorPower Φ k)
        (KrausChannel.tensorPower Φ l))).toLinearMap =
      (KrausChannel.tensorPower Φ (k + l)).toLinearMap := by
  apply MatrixMap.choi_injective
  exact tensorPower_add_choi Φ k l

/-- The power-splitting identity as a direct action on arbitrary input matrices. -/
theorem tensorPower_add_apply (Φ : KrausChannel n m) (k l : ℕ)
    (X : Operator (n ^ k * n ^ l)) :
    (KrausChannel.tensorPower Φ (k + l)).apply
      (Matrix.reindex (channelAddEquiv n k l) (channelAddEquiv n k l) X) =
      Matrix.reindex (channelAddEquiv m k l) (channelAddEquiv m k l)
        ((KrausChannel.tensor (KrausChannel.tensorPower Φ k)
          (KrausChannel.tensorPower Φ l)).apply X) := by
  change (KrausChannel.tensorPower Φ (k + l)).toLinearMap _ = _
  rw [← tensorPower_add_toLinearMap]
  exact reindexChannel_apply _ _ _ _

end QuantumChannelStein.ChannelPowerReindex
