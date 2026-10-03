import QuantumChannelStein.ChannelEntropy

/-!
# Choi states and one-use channel-divergence finiteness

The normalized maximally entangled input is constructed explicitly. Its
actual amplified output is the Choi matrix divided by the input dimension.
This connects the optimized channel divergence to the checked finite-state
support criterion, with no assumption about a regularized limit.
-/

noncomputable section
namespace QuantumChannelStein.ChannelEntropy

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n m : ℕ}

/-- The normalized maximally entangled vector, totalized at dimension zero
only as an auxiliary vector. Normalized inputs require `0 < n`. -/
def maximallyEntangledVector (n : ℕ) : EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => if p.1 = p.2 then (Real.sqrt ((n : ℝ)⁻¹) : ℂ) else 0)

theorem norm_maximallyEntangledVector (hn : 0 < n) :
    ‖maximallyEntangledVector n‖ = 1 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hs : ‖maximallyEntangledVector n‖ ^ 2 = 1 := by
    simp [EuclideanSpace.norm_sq_eq, maximallyEntangledVector, Fintype.sum_prod_type,
      apply_ite, hnR]
  nlinarith [norm_nonneg (maximallyEntangledVector n)]

/-- An explicit allowed maximally entangled pure input. -/
def maximallyEntangledInput (hn : 0 < n) : UnitPureInput n n :=
  ⟨maximallyEntangledVector n, norm_maximallyEntangledVector hn⟩

/-- Its rank-one density matrix is the unnormalized entangled matrix
divided by the input dimension. -/
theorem pureMatrix_maximallyEntangledVector (n : ℕ) :
    pureMatrix (maximallyEntangledVector n) =
      (n : ℝ)⁻¹ • MatrixMap.maximallyEntangled n := by
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hij : i = j <;> by_cases hkl : k = l <;>
    simp [pureMatrix, maximallyEntangledVector, MatrixMap.maximallyEntangled,
      Matrix.vecMulVec, hij, hkl]
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  simp

/-- Real scalar multiplication commutes with the actual Kraus extension. -/
theorem amplify_real_smul (Φ : KrausChannel n m) (r : ℕ) (t : ℝ)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) :
    Φ.amplify r (t • X) = t • Φ.amplify r X := by
  simp only [KrausChannel.amplify, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- The maximally entangled output is exactly the normalized Choi matrix. -/
theorem amplify_maximallyEntangledVector (Φ : KrausChannel n m) :
    Φ.amplify n (pureMatrix (maximallyEntangledVector n)) = (n : ℝ)⁻¹ • Φ.choi := by
  rw [pureMatrix_maximallyEntangledVector, amplify_real_smul,
    ← MatrixMap.amplify_toLinearMap, MatrixMap.amplify_maximallyEntangled,
    MatrixMap.choi_toLinearMap]

/-- The normalized Choi density matrix, using the actual maximally
entangled reference-assisted output and canonical finite-index flattening. -/
def normalizedChoiState (Φ : KrausChannel n m) (hn : 0 < n) : State (n * m) :=
  pureOutput Φ (maximallyEntangledInput hn)

theorem normalizedChoiState_matrix (Φ : KrausChannel n m) (hn : 0 < n) :
    (normalizedChoiState Φ hn).matrix =
      Matrix.reindex finProdFinEquiv finProdFinEquiv ((n : ℝ)⁻¹ • Φ.choi) := by
  change Matrix.reindex _ _ (Φ.amplify n (pureMatrix (maximallyEntangledVector n))) = _
  rw [amplify_maximallyEntangledVector]

/-- Optimizing over pure inputs includes the normalized Choi pair. -/
theorem umegaki_normalizedChoi_le_channelD (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    RelativeEntropy.umegaki (normalizedChoiState Φ hn) (normalizedChoiState Ψ hn) ≤
      channelD Φ Ψ :=
  umegaki_pureOutput_le_channelD Φ Ψ (maximallyEntangledInput hn)

/-- Nonzero real rescaling does not change an operator's kernel. -/
theorem ker_real_smul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (t : ℝ) (ht : t ≠ 0) :
    LinearMap.ker (t • A).mulVecLin = LinearMap.ker A.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.smul_mulVec,
    smul_eq_zero, ht, false_or]

/-- A strictly positive scalar does not change positive semidefiniteness. -/
theorem posSemidef_real_smul_iff {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (t : ℝ) (ht : 0 < t) :
    (t • A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using
      h.smul (inv_nonneg.mpr ht.le)
  · exact fun h => h.smul ht.le

/-- Flattening and normalization cancel from a Choi domination statement. -/
theorem normalizedChoi_domination_iff (Φ Ψ : KrausChannel n m) (hn : 0 < n) (c : ℝ) :
    (c • (normalizedChoiState Ψ hn).matrix - (normalizedChoiState Φ hn).matrix).PosSemidef ↔
      (c • Ψ.choi - Φ.choi).PosSemidef := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have heq : c • (normalizedChoiState Ψ hn).matrix -
      (normalizedChoiState Φ hn).matrix =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((n : ℝ)⁻¹ • (c • Ψ.choi - Φ.choi)) := by
    rw [normalizedChoiState_matrix, normalizedChoiState_matrix]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_sub, smul_comm c (n : ℝ)⁻¹]
  rw [heq]
  change (((n : ℝ)⁻¹ • (c • Ψ.choi - Φ.choi)).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm).PosSemidef ↔ _
  rw [Matrix.posSemidef_submatrix_equiv]
  exact posSemidef_real_smul_iff _ _ (inv_pos.mpr hnR)

/-- Support inclusion of normalized Choi states is exactly support
inclusion of the original unnormalized Choi matrices. -/
theorem normalizedChoi_support_iff (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    RelativeEntropy.supportIncluded (normalizedChoiState Φ hn) (normalizedChoiState Ψ hn) ↔
      LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin := by
  rw [RelativeEntropy.supportIncluded_iff_exists_domination,
    SupportDomination.ker_le_iff_exists_domination Φ.choi_positive Ψ.choi_positive]
  simp only [normalizedChoi_domination_iff]

/-- Choi PSD domination is precisely CP domination of the channel maps. -/
theorem choi_domination_iff_cpLe (Φ Ψ : KrausChannel n m) (c : ℝ) :
    (c • Ψ.choi - Φ.choi).PosSemidef ↔
      MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap) := by
  rw [MatrixMap.cpLe_iff_choi_difference, MatrixMap.choi_smul,
    MatrixMap.choi_toLinearMap, MatrixMap.choi_toLinearMap]
  rfl

/-- Choi support inclusion is equivalent to existence of a finite CP
scalar domination constant at least one. -/
theorem choi_support_iff_exists_cpLe (Φ Ψ : KrausChannel n m) :
    LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin ↔
      ∃ c : ℝ, 1 ≤ c ∧ MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap) := by
  rw [SupportDomination.ker_le_iff_exists_domination Φ.choi_positive Ψ.choi_positive]
  simp only [choi_domination_iff_cpLe]

/-- The actual one-use optimized channel divergence is finite exactly
when the first Choi support is contained in the second Choi support. -/
theorem channelD_lt_top_iff_choi_support (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    channelD Φ Ψ < ⊤ ↔
      LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin := by
  constructor
  · intro h
    apply (normalizedChoi_support_iff Φ Ψ hn).mp
    apply (RelativeEntropy.umegaki_lt_top_iff _ _).mp
    exact lt_of_le_of_lt (umegaki_normalizedChoi_le_channelD Φ Ψ hn) h
  · intro h
    obtain ⟨c, hc, hcp⟩ := (choi_support_iff_exists_cpLe Φ Ψ).mp h
    exact channelD_lt_top_of_cpLe Φ Ψ c hc hcp

/-- An equivalent finiteness criterion using completely positive order. -/
theorem channelD_lt_top_iff_exists_cpLe (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    channelD Φ Ψ < ⊤ ↔
      ∃ c : ℝ, 1 ≤ c ∧ MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap) := by
  rw [channelD_lt_top_iff_choi_support Φ Ψ hn, choi_support_iff_exists_cpLe]

/-- A missing Choi support direction makes the channel divergence
infinite, witnessed by the explicit maximally entangled input. -/
theorem channelD_eq_top_of_not_choi_support (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (h : ¬ LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin) :
    channelD Φ Ψ = ⊤ := by
  apply top_unique
  have hs : ¬ RelativeEntropy.supportIncluded
      (normalizedChoiState Φ hn) (normalizedChoiState Ψ hn) :=
    fun hs => h ((normalizedChoi_support_iff Φ Ψ hn).mp hs)
  have ht := RelativeEntropy.umegaki_of_not_supportIncluded _ _ hs
  rw [← ht]
  exact umegaki_normalizedChoi_le_channelD Φ Ψ hn

end QuantumChannelStein.ChannelEntropy
