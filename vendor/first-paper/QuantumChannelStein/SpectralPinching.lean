import QuantumChannelStein.PinchingGramBound
import QuantumChannelStein.SpectralDecompositionCFC
import QuantumChannelStein.SharpDataProcessing
import QuantumChannelStein.ChannelEntropyRates

/-! # Genuine spectral pinching by distinct alternative eigenvalues

There is one actual Kraus projection per distinct eigenvalue, including zero.
The pinching constant is the exact spectrum cardinality, not the Hilbert dimension.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SpectralPinching
open Matrix SpectralDecomposition ChannelEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

def eigenvalueSet (σ : State n) : Finset ℝ := by
  classical
  exact Finset.univ.image σ.positive.isHermitian.eigenvalues

abbrev Block (σ : State n) := ↥(eigenvalueSet σ)

def eigenvalueIndex (σ : State n) (i : Fin n) : Block σ :=
  ⟨σ.positive.isHermitian.eigenvalues i, by
    classical
    simp [eigenvalueSet]⟩

def blockDiagonal (σ : State n) (v : Block σ) : Fin n → ℂ := by
  classical
  exact fun i => if σ.positive.isHermitian.eigenvalues i = v.val then 1 else 0

def projection (σ : State n) (v : Block σ) : Operator n :=
  diagonalHom σ.positive.isHermitian.eigenvectorUnitary (blockDiagonal σ v)

theorem projection_hermitian (σ : State n) (v : Block σ) : (projection σ v).IsHermitian := by
  classical
  change star (diagonalHom σ.positive.isHermitian.eigenvectorUnitary (blockDiagonal σ v)) = _
  rw [← map_star]
  congr 1
  ext i
  simp [blockDiagonal, apply_ite]

theorem projection_square (σ : State n) (v : Block σ) : projection σ v * projection σ v = projection σ v := by
  classical
  unfold projection
  rw [← map_mul]
  congr 1
  ext i
  by_cases hi : σ.positive.isHermitian.eigenvalues i = v.val <;> simp [blockDiagonal, hi]

theorem sum_projection (σ : State n) : ∑ v : Block σ, projection σ v = 1 := by
  classical
  unfold projection
  rw [← map_sum]
  have hd : (∑ v : Block σ, blockDiagonal σ v) = 1 := by
    ext i
    simp only [Finset.sum_apply, Pi.one_apply]
    have hterm (v : Block σ) : blockDiagonal σ v i = if eigenvalueIndex σ i = v then 1 else 0 := by
      simp only [blockDiagonal, Subtype.ext_iff, eigenvalueIndex]
    simp only [hterm]
    simp
  rw [hd, map_one]

theorem diagonalHom_eigenvalues (σ : State n) :
    diagonalHom σ.positive.isHermitian.eigenvectorUnitary
      (fun i => (σ.positive.isHermitian.eigenvalues i : ℂ)) = σ.matrix := by
  symm
  simpa only [diagonalHom, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    using σ.positive.isHermitian.spectral_theorem

theorem sigma_mul_projection (σ : State n) (v : Block σ) :
    σ.matrix * projection σ v = (v.val : ℂ) • projection σ v := by
  classical
  rw [← diagonalHom_eigenvalues σ]
  unfold projection
  rw [← map_mul]
  have hd : (fun i => (σ.positive.isHermitian.eigenvalues i : ℂ)) * blockDiagonal σ v =
      (v.val : ℂ) • blockDiagonal σ v := by
    ext i
    by_cases hi : σ.positive.isHermitian.eigenvalues i = v.val <;> simp [blockDiagonal, hi]
  rw [hd, map_smul]

theorem projection_mul_sigma (σ : State n) (v : Block σ) :
    projection σ v * σ.matrix = (v.val : ℂ) • projection σ v := by
  rw [← sigma_mul_projection σ v, ← diagonalHom_eigenvalues σ]
  unfold projection
  rw [← map_mul, ← map_mul, mul_comm]

/-- The literal normalized Kraus channel with one block projection per distinct eigenvalue. -/
def channel (σ : State n) : KrausChannel n n where
  rank := Fintype.card (Block σ)
  kraus i := projection σ ((Fintype.equivFin (Block σ)).symm i)
  normalized := by
    rw [← Equiv.sum_comp (Fintype.equivFin (Block σ))]
    simp only [Equiv.symm_apply_apply, (projection_hermitian σ _).eq, projection_square, sum_projection]

theorem channel_apply (σ : State n) (A : Operator n) :
    (channel σ).apply A = ∑ v : Block σ, projection σ v * A * projection σ v := by
  unfold KrausChannel.apply channel
  rw [← Equiv.sum_comp (Fintype.equivFin (Block σ))]
  simp only [Equiv.symm_apply_apply, (projection_hermitian σ _).eq]

theorem channel_fixes_sigma (σ : State n) : (channel σ).apply σ.matrix = σ.matrix := by
  rw [channel_apply]
  have ht (v : Block σ) : projection σ v * σ.matrix * projection σ v = σ.matrix * projection σ v := by
    rw [projection_mul_sigma, ← sigma_mul_projection]
    rw [Matrix.mul_assoc, projection_square]
  simp only [ht, ← Matrix.mul_sum, sum_projection, Matrix.mul_one]

theorem channel_onState_sigma (σ : State n) : (channel σ).onState σ = σ := by
  apply state_eq_of_matrix_eq
  exact channel_fixes_sigma σ

/-- Every pinched matrix commutes with the alternative, with no invertibility assumption. -/
theorem channel_apply_commutes (σ : State n) (A : Operator n) : Commute σ.matrix ((channel σ).apply A) := by
  change σ.matrix * (channel σ).apply A = (channel σ).apply A * σ.matrix
  rw [channel_apply, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Matrix.mul_assoc σ.matrix, ← Matrix.mul_assoc σ.matrix, sigma_mul_projection,
    Matrix.smul_mul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc, projection_mul_sigma, Matrix.mul_smul]

/-- Pinching inequality with the exact number of distinct eigenvalues. -/
theorem domination (σ : State n) (A : Operator n) (hA : A.PosSemidef) :
    (((Fintype.card (Block σ) : ℝ) • (channel σ).apply A) - A).PosSemidef := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hsum : (∑ v : Block σ, projection σ v * S) = S := by
    rw [← Matrix.sum_mul, sum_projection, Matrix.one_mul]
  have hg (v : Block σ) : (projection σ v * S) * (projection σ v * S)ᴴ =
      projection σ v * A * projection σ v := by
    rw [Matrix.conjTranspose_mul, hS.eq, (projection_hermitian σ v).eq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S S, hSS]
  have h := gram_sum_le_card (fun v : Block σ => projection σ v * S)
  rw [hsum, hS.eq, hSS] at h
  simpa only [hg, ← channel_apply] using h

/-- The constant is exactly the cardinality of the real spectrum. -/
theorem block_card_eq_real_spectrum (σ : State n) :
    Fintype.card (Block σ) = (spectrum ℝ σ.matrix).ncard := by
  classical
  rw [σ.positive.isHermitian.spectrum_real_eq_range_eigenvalues]
  have he : (eigenvalueSet σ : Set ℝ) = Set.range σ.positive.isHermitian.eigenvalues := by
    simp [eigenvalueSet]
  rw [← he, Set.ncard_coe_finset]
  exact Fintype.card_coe _

/-- The same constant is the complex-spectrum cardinality used by the polynomial invariant-algebra bound. -/
theorem block_card_eq_complex_spectrum (σ : State n) :
    Fintype.card (Block σ) = (spectrum ℂ σ.matrix).ncard := by
  rw [σ.positive.isHermitian.spectrum_eq_image_range]
  change Fintype.card (Block σ) = (Complex.ofReal '' Set.range σ.positive.isHermitian.eigenvalues).ncard
  rw [Set.ncard_image_of_injective _ Complex.ofReal_injective,
    block_card_eq_real_spectrum, σ.positive.isHermitian.spectrum_real_eq_range_eigenvalues]

end QuantumChannelStein.SpectralPinching
