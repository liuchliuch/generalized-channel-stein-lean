import QuantumChannelStein.ExponentialStinespring
import QuantumChannelStein.DiamondNorm
import QuantumChannelStein.SandwichedQuasiExtended

/-!
# Actual purification-matrix decomposition for the Rényi continuity estimate

All factors are reshaped outputs of the prescribed reference-extended
Stinespring matrices. Their Frobenius norms are proved to be the Euclidean
norms of these output vectors, with exact output/environment coordinates.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.PurificationDecomposition
open Matrix ChannelEntropy ReferenceAcceptance TensorNorm SandwichedRenyi
  EnvironmentTensor ChannelDilationPower UniformApproximation
open scoped BigOperators Kronecker Matrix.Norms.L2Operator ComplexOrder
variable {a b e eN eM r : ℕ}

/-- Reshape the genuine dilation output vector into output/environment columns. -/
def amplitude (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (ψ : EuclideanSpace ℂ (Fin r × Fin a)) : Matrix (Fin (r * b)) (Fin e) ℂ :=
  fun i j => matrixMap (dilation (r := Fin r) V) ψ (finProdFinEquiv.symm i, j)

/-- Its Gram matrix is exactly the output marginal of the dilation vector. -/
theorem amplitude_gram (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (ψ : EuclideanSpace ℂ (Fin r × Fin a)) :
    amplitude V ψ * (amplitude V ψ)ᴴ =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (traceEnvironment (pureMatrix (matrixMap (dilation (r := Fin r) V) ψ))) := by
  ext i j
  simp [amplitude, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.reindex_apply,
    traceEnvironment, pureMatrix, Matrix.vecMulVec]

/-- The factor really purifies the specified channel's actual amplified output. -/
theorem amplitude_gram_eq_output (Φ : KrausChannel a b)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : dilationMap V = Φ.toLinearMap)
    (ψ : UnitPureInput r a) :
    amplitude V ψ.val * (amplitude V ψ.val)ᴴ = (pureOutput Φ ψ).matrix := by
  rw [amplitude_gram, matrixMap_apply, ← conjugate_pureMatrix,
    ← DiamondNorm.amplify_dilationMap, hV, MatrixMap.amplify_toLinearMap]
  rfl

/-- Frobenius norm is exactly the norm of the genuine output vector. -/
theorem frobeniusNorm_amplitude (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (ψ : EuclideanSpace ℂ (Fin r × Fin a)) :
    frobeniusNorm (amplitude V ψ) = ‖matrixMap (dilation (r := Fin r) V) ψ‖ := by
  have hsq : frobeniusNorm (amplitude V ψ) ^ 2 =
      ‖matrixMap (dilation (r := Fin r) V) ψ‖ ^ 2 := by
    rw [frobeniusNorm_sq, amplitude_gram, trace_reindex_equiv]
    have htrace : (traceEnvironment (pureMatrix (matrixMap (dilation (r := Fin r) V) ψ))).trace =
        (pureMatrix (matrixMap (dilation (r := Fin r) V) ψ)).trace := by
      simp [traceEnvironment, Matrix.trace, Fintype.sum_prod_type]
    rw [htrace, trace_pureMatrix_re]
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp hsq

/-- Uniform operator error controls this genuine Frobenius factor norm. -/
theorem frobeniusNorm_amplitude_le (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (ψ : UnitPureInput r a) : frobeniusNorm (amplitude V ψ.val) ≤ ‖V‖ := by
  rw [frobeniusNorm_amplitude]
  have h := (matrixMap (dilation (r := Fin r) V)).le_opNorm ψ.val
  rw [ψ.property, mul_one, matrixMap_norm] at h
  exact h.trans (dilation_opNorm_le V)

/-- Linear subtraction in the actual dilation gives linear subtraction of factors. -/
theorem amplitude_sub (V W : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (ψ : EuclideanSpace ℂ (Fin r × Fin a)) :
    amplitude (V - W) ψ = amplitude V ψ - amplitude W ψ := by
  ext i j
  simp [amplitude, dilation_sub, matrixMap_sub]

/-- An environment map acts on the purification columns by ordinary transpose. -/
theorem amplitude_environment (V : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (C : Matrix (Fin eN) (Fin eM) ℂ) (ψ : EuclideanSpace ℂ (Fin r × Fin a)) :
    amplitude (applyEnvironment V C) ψ = amplitude V ψ * Cᵀ := by
  ext i j
  simp only [amplitude, applyEnvironment, dilation_environment, matrixMap_mul,
    ContinuousLinearMap.comp_apply, matrixMap_apply]
  simp [amplitude, matrixMap_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, mul_comm, Matrix.one_apply, Fintype.sum_prod_type]

/-- A genuine bounded column operation gives the required PSD factor domination. -/
theorem factor_gram_domination (F : Matrix (Fin (r * b)) (Fin eM) ℂ)
    (C : Matrix (Fin eN) (Fin eM) ℂ) (t : ℝ) (ht : 0 ≤ t) (hC : ‖C‖ ^ 2 ≤ t) :
    (t • (F * Fᴴ) - (F * Cᵀ) * (F * Cᵀ)ᴴ).PosSemidef := by
  have hp := DominatedSubchannels.gram_le_scalar_of_norm_sq_le Cᵀ ht
    (by simpa only [TransposeNorm.opNorm_transpose] using hC)
  have h := hp.mul_mul_conjTranspose_same F
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

/-- The exact purification factor of a channel output has Frobenius norm one. -/
theorem frobeniusNorm_amplitude_channel (Φ : KrausChannel a b)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : dilationMap V = Φ.toLinearMap)
    (ψ : UnitPureInput r a) : frobeniusNorm (amplitude V ψ.val) = 1 := by
  have hs := frobeniusNorm_sq (amplitude V ψ.val)
  rw [amplitude_gram_eq_output Φ V hV ψ, (pureOutput Φ ψ).trace_one] at hs
  have hn : 0 ≤ frobeniusNorm (amplitude V ψ.val) := Real.sqrt_nonneg _
  change frobeniusNorm (amplitude V ψ.val) ^ 2 = 1 at hs
  nlinarith

/-- One-shot actual factor splitting with a shared prescribed environment.
The residual has its own genuine CP-domination and Hilbert/Frobenius error. -/
theorem one_shot_decomposition (Φ Ψ : KrausChannel a b)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (C D : Matrix (Fin eN) (Fin eM) ℂ) (hexact : VN = applyEnvironment VM D)
    (t₀ t₁ δ : ℝ) (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁)
    (hC : ‖C‖ ^ 2 ≤ t₀) (hDC : ‖D - C‖ ^ 2 ≤ t₁)
    (herr : ‖VN - applyEnvironment VM C‖ ≤ δ) (ψ : UnitPureInput r a) :
    ∃ F₀ F₁ : Matrix (Fin (r * b)) (Fin eN) ℂ,
      (pureOutput Φ ψ).matrix = (F₀ + F₁) * (F₀ + F₁)ᴴ ∧
      (t₀ • (pureOutput Ψ ψ).matrix - F₀ * F₀ᴴ).PosSemidef ∧
      (t₁ • (pureOutput Ψ ψ).matrix - F₁ * F₁ᴴ).PosSemidef ∧
      frobeniusNorm F₀ ≤ 1 + δ ∧ frobeniusNorm F₁ ≤ δ := by
  let F₀ := amplitude (applyEnvironment VM C) ψ.val
  let F₁ := amplitude (VN - applyEnvironment VM C) ψ.val
  have hsum : F₀ + F₁ = amplitude VN ψ.val := by
    dsimp [F₀, F₁]
    rw [amplitude_sub]
    abel
  have h₀ : F₀ = amplitude VM ψ.val * Cᵀ := amplitude_environment VM C ψ.val
  have hres : VN - applyEnvironment VM C = applyEnvironment VM (D - C) := by
    rw [hexact]
    exact ((environmentLinear VM).map_sub D C).symm
  have h₁ : F₁ = amplitude VM ψ.val * (D - C)ᵀ := by
    dsimp [F₁]
    rw [hres, amplitude_environment]
  have hnorm₁ : frobeniusNorm F₁ ≤ δ := (frobeniusNorm_amplitude_le _ ψ).trans herr
  refine ⟨F₀, F₁, ?_, ?_, ?_, ?_, hnorm₁⟩
  · rw [hsum, amplitude_gram_eq_output Φ VN hVN ψ]
  · rw [h₀, ← amplitude_gram_eq_output Ψ VM hVM ψ]
    exact factor_gram_domination _ C t₀ ht₀ hC
  · rw [h₁, ← amplitude_gram_eq_output Ψ VM hVM ψ]
    exact factor_gram_domination _ (D - C) t₁ ht₁ hDC
  · have htriangle : frobeniusNorm F₀ ≤ frobeniusNorm (amplitude VN ψ.val) + frobeniusNorm F₁ := by
      have hvec : frobeniusVector F₀ =
          frobeniusVector (amplitude VN ψ.val) - frobeniusVector F₁ := by
        rw [← hsum]
        ext i
        simp [frobeniusVector]
      simp only [frobeniusNorm_eq_vector_norm]
      rw [hvec]
      exact norm_sub_le _ _
    rw [frobeniusNorm_amplitude_channel Φ VN hVN ψ] at htriangle
    exact htriangle.trans (add_le_add le_rfl hnorm₁)

end QuantumChannelStein.PurificationDecomposition
