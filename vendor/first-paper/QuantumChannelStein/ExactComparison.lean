import QuantumChannelStein.Reshaping
import QuantumChannelStein.Factorization
import QuantumChannelStein.CPOrder

/-!
# Exact comparison in fixed environment spaces

Corollary 3.3 of arXiv:2609.27196. The maps are explicitly defined by the
prescribed dilation matrices; no change or enlargement of environments occurs.
-/
noncomputable section
namespace QuantumChannelStein
open scoped BigOperators ComplexOrder Kronecker Matrix.Norms.L2Operator
open Matrix

/-- The CP matrix map represented by an arbitrary fixed dilation matrix. -/
def dilationMap {a b e : ℕ} (V : Matrix (Fin b × Fin e) (Fin a) ℂ) : MatrixMap a b :=
  MatrixMap.ofKraus (fun k i j => V (i, k) j)

/-- This representation is exactly conjugation followed by discarding the environment. -/
theorem dilationMap_apply {a b e : ℕ} (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (X : Operator a) :
    dilationMap V X = KrausChannel.traceEnvironment (V * X * Vᴴ) := by
  ext i j
  simp [dilationMap, MatrixMap.ofKraus, KrausChannel.traceEnvironment,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The Choi operator is the Gram matrix of the prescribed dilation columns. -/
theorem choi_dilationMap {a b e : ℕ} (V : Matrix (Fin b × Fin e) (Fin a) ℂ) :
    MatrixMap.choi (dilationMap V) = dilationColumns V * (dilationColumns V)ᴴ := by
  rw [dilationMap, MatrixMap.choi_ofKraus]
  rfl

/-- Gram domination gives an exact auxiliary map without changing environments. -/
theorem exact_auxiliary_map_of_gram {a b eN eM : ℕ}
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    {c : ℝ} (hc : 0 ≤ c)
    (h : (c • (dilationColumns VM * (dilationColumns VM)ᴴ) -
      dilationColumns VN * (dilationColumns VN)ᴴ).PosSemidef) :
    ∃ C : Matrix (Fin eN) (Fin eM) ℂ,
      VN = ((1 : Operator b) ⊗ₖ C) * VM ∧ ‖C‖ ≤ Real.sqrt c := by
  obtain ⟨D, hD, hnorm⟩ := Factorization.matrix_factorization
    (dilationColumns VN) (dilationColumns VM) hc h
  refine ⟨Dᵀ, environmental_comparison_of_columns VN VM D hD, ?_⟩
  rwa [TransposeNorm.opNorm_transpose]

/-- **Corollary 3.3 (Exact auxiliary map).** CP domination of the maps
represented by two fixed dilations supplies an auxiliary environmental map
of norm at most `sqrt c`. The result in fact holds for all dilation matrices,
so it includes the isometries required in the paper without adding assumptions. -/
theorem exact_auxiliary_map {a b eN eM : ℕ}
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    {c : ℝ} (hc : 1 ≤ c)
    (h : MatrixMap.CPLe (dilationMap VN) ((c : ℂ) • dilationMap VM)) :
    ∃ C : Matrix (Fin eN) (Fin eM) ℂ,
      VN = ((1 : Operator b) ⊗ₖ C) * VM ∧ ‖C‖ ≤ Real.sqrt c := by
  apply exact_auxiliary_map_of_gram VN VM (le_trans zero_le_one hc)
  rw [MatrixMap.cpLe_iff_choi_difference, MatrixMap.choi_smul,
    choi_dilationMap, choi_dilationMap] at h
  simpa only [Complex.real_smul] using h

end QuantumChannelStein
