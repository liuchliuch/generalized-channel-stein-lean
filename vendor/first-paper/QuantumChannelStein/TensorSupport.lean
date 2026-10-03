import QuantumChannelStein.TensorMap
import QuantumChannelStein.SupportDomination

/-! # Support reflection for tensor products -/
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

/-- Entrywise tensor product of two coordinate vectors. -/
def vectorTensor {ι κ : Type*} (x : ι → ℂ) (y : κ → ℂ) : ι × κ → ℂ :=
  fun i => x i.1 * y i.2

/-- Product matrices act independently on product vectors. -/
theorem kronecker_mulVec_vectorTensor {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (x : ι → ℂ) (y : κ → ℂ) :
    (A ⊗ₖ B) *ᵥ vectorTensor x y = vectorTensor (A *ᵥ x) (B *ᵥ y) := by
  ext ⟨i,j⟩
  simp [vectorTensor, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Finset.mul_sum, mul_comm, mul_left_comm]
  rw [Finset.sum_comm]

/-- Kernel inclusion of a tensor product reflects to the first factor,
provided its second null-hypothesis factor is nonzero. -/
theorem kernel_inclusion_of_tensor {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A B : Matrix ι ι ℂ) (C D : Matrix κ κ ℂ) (hC : C ≠ 0)
    (h : LinearMap.ker (B ⊗ₖ D).mulVecLin ≤ LinearMap.ker (A ⊗ₖ C).mulVecLin) :
    LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  have hex : ∃ i j, C i j ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply hC
    ext i j
    exact hh i j
  obtain ⟨i,j,hij⟩ := hex
  intro x hx
  have hx0 : B *ᵥ x = 0 := LinearMap.mem_ker.mp hx
  have ht : vectorTensor x (Pi.single j 1) ∈ LinearMap.ker (B ⊗ₖ D).mulVecLin := by
    apply LinearMap.mem_ker.mpr
    change (B ⊗ₖ D) *ᵥ vectorTensor x (Pi.single j 1) = 0
    rw [kronecker_mulVec_vectorTensor, hx0]
    ext z
    simp [vectorTensor]
  have hzero : (A ⊗ₖ C) *ᵥ vectorTensor x (Pi.single j 1) = 0 := LinearMap.mem_ker.mp (h ht)
  rw [kronecker_mulVec_vectorTensor] at hzero
  apply LinearMap.mem_ker.mpr
  ext k
  have hk := congrFun hzero (k,i)
  change (A *ᵥ x) k * (C *ᵥ Pi.single j 1) i = 0 at hk
  have hCi : (C *ᵥ Pi.single j 1) i = C i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hCi] at hk
  exact (mul_eq_zero.mp hk).resolve_right hij


/-- A common bijective reindexing preserves a scalar PSD comparison. -/
theorem reindex_domination_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A B : Matrix ι ι ℂ) (c : ℝ) :
    (c • Matrix.reindex e e B - Matrix.reindex e e A).PosSemidef ↔
      (c • B - A).PosSemidef := by
  change ((c • B - A).submatrix e.symm e.symm).PosSemidef ↔ _
  exact Matrix.posSemidef_submatrix_equiv e.symm

/-- The PSD support relation is invariant under an actual coordinate permutation. -/
theorem reindex_kernel_inclusion_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    LinearMap.ker (Matrix.reindex e e B).mulVecLin ≤
      LinearMap.ker (Matrix.reindex e e A).mulVecLin ↔
    LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  have hA' : (Matrix.reindex e e A).PosSemidef := hA.submatrix e.symm
  have hB' : (Matrix.reindex e e B).PosSemidef := hB.submatrix e.symm
  rw [SupportDomination.ker_le_iff_exists_domination hA' hB',
    SupportDomination.ker_le_iff_exists_domination hA hB]
  simp only [reindex_domination_iff]

/-- A channel with positive input dimension has nonzero unnormalized Choi matrix. -/
theorem KrausChannel.choi_ne_zero {n m : ℕ} (Φ : KrausChannel n m) (hn : 0 < n) : Φ.choi ≠ 0 := by
  intro h
  have ht := Φ.traceOutput_choi
  rw [h] at ht
  have hi := congrFun (congrFun ht (⟨0,hn⟩ : Fin n)) (⟨0,hn⟩ : Fin n)
  simp [KrausChannel.traceOutput] at hi

/-- Tensor-channel Choi support inclusion reflects to the first channel pair.
The second null channel only needs a positive input dimension. -/
theorem KrausChannel.choi_support_of_tensor {n m a b : ℕ}
    (Φ Ψ : KrausChannel n m) (Γ Θ : KrausChannel a b) (ha : 0 < a)
    (h : LinearMap.ker (KrausChannel.tensor Ψ Θ).choi.mulVecLin ≤
      LinearMap.ker (KrausChannel.tensor Φ Γ).choi.mulVecLin) :
    LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin := by
  have hN := MatrixMap.posSemidef_kronecker Φ.choi_positive Γ.choi_positive
  have hM := MatrixMap.posSemidef_kronecker Ψ.choi_positive Θ.choi_positive
  have hΦ : (KrausChannel.tensor Φ Γ).choi =
      Matrix.reindex (MatrixMap.choiShuffle n m a b) (MatrixMap.choiShuffle n m a b)
        (Φ.choi ⊗ₖ Γ.choi) := by
    rw [← MatrixMap.choi_toLinearMap, ← MatrixMap.tensor_kraus_toLinearMap,
      MatrixMap.choi_tensor, MatrixMap.choi_toLinearMap, MatrixMap.choi_toLinearMap]
  have hΨ : (KrausChannel.tensor Ψ Θ).choi =
      Matrix.reindex (MatrixMap.choiShuffle n m a b) (MatrixMap.choiShuffle n m a b)
        (Ψ.choi ⊗ₖ Θ.choi) := by
    rw [← MatrixMap.choi_toLinearMap, ← MatrixMap.tensor_kraus_toLinearMap,
      MatrixMap.choi_tensor, MatrixMap.choi_toLinearMap, MatrixMap.choi_toLinearMap]
  rw [hΦ, hΨ] at h
  have hraw := (reindex_kernel_inclusion_iff (MatrixMap.choiShuffle n m a b) _ _ hN hM).mp h
  exact kernel_inclusion_of_tensor Φ.choi Ψ.choi Γ.choi Θ.choi (Γ.choi_ne_zero ha) hraw


/-- Dimension casts do not alter the Choi support relation. -/
theorem KrausChannel.choi_support_cast_iff {n m n' m' : ℕ}
    (Φ Ψ : KrausChannel n m) (hn : n = n') (hm : m = m') :
    LinearMap.ker (Ψ.cast hn hm).choi.mulVecLin ≤ LinearMap.ker (Φ.cast hn hm).choi.mulVecLin ↔
      LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin := by
  cases hn
  cases hm
  rfl

/-- Support inclusion for any positive number of independent uses implies
support inclusion already for one use. -/
theorem KrausChannel.choi_support_of_tensorPower {n m : ℕ}
    (Φ Ψ : KrausChannel n m) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (h : LinearMap.ker (KrausChannel.tensorPower Ψ k).choi.mulVecLin ≤
      LinearMap.ker (KrausChannel.tensorPower Φ k).choi.mulVecLin) :
    LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin := by
  cases k with
  | zero => omega
  | succ k =>
    have hraw := (KrausChannel.choi_support_cast_iff
      (KrausChannel.tensor Φ (KrausChannel.tensorPower Φ k))
      (KrausChannel.tensor Ψ (KrausChannel.tensorPower Ψ k)) _ _).mp h
    exact KrausChannel.choi_support_of_tensor Φ Ψ _ _ (Nat.pow_pos hn) hraw

/-- A missing support direction persists through every positive tensor power. -/
theorem KrausChannel.not_choi_support_tensorPower {n m : ℕ}
    (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (h : ¬ LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin)
    (k : ℕ) (hk : 0 < k) :
    ¬ LinearMap.ker (KrausChannel.tensorPower Ψ k).choi.mulVecLin ≤
      LinearMap.ker (KrausChannel.tensorPower Φ k).choi.mulVecLin :=
  fun ht => h (KrausChannel.choi_support_of_tensorPower Φ Ψ hn k hk ht)

end QuantumChannelStein


