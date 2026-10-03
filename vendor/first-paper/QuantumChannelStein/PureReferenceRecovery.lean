import QuantumChannelStein.KrausRecovery
import QuantumChannelStein.ChannelLocality
import QuantumChannelStein.TestingPrimal

/-! # Exact reference-channel recovery from a canonical finite purification

A rectangular Douglas factorization supplies a contraction from an input-sized
reference. Its explicit trace-preserving completion recovers the original
pure input exactly, because the positive remainder has trace zero.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.PureReferenceRecovery
open Matrix ChannelEntropy OperationalTesting ChannelLocality SpectralDecomposition
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {r s n m : ℕ}

def coefficientMatrix (ψ : UnitPureInput r n) : Matrix (Fin r) (Fin n) ℂ :=
  fun i j => ψ.val (i,j)

theorem coefficient_gram_trace (ψ : UnitPureInput r n) :
    ((coefficientMatrix ψ)ᴴ * coefficientMatrix ψ).trace = 1 := by
  have hnorm : ‖ψ.val‖ ^ 2 = ((coefficientMatrix ψ)ᴴ * coefficientMatrix ψ).trace.re := by
    rw [Matrix.trace_mul_comm]
    simp [EuclideanSpace.norm_sq_eq, coefficientMatrix, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, ← Complex.normSq_eq_norm_sq,
      Complex.mul_conj]
  apply Complex.ext
  · rw [ψ.property] at hnorm
    norm_num at hnorm ⊢
    exact hnorm.symm
  · exact (Complex.nonneg_iff.mp
      (Matrix.posSemidef_conjTranspose_mul_self (coefficientMatrix ψ)).trace_nonneg).2.symm

def inputDensity (ψ : UnitPureInput r n) : State n where
  matrix := (coefficientMatrix ψ)ᴴ * coefficientMatrix ψ
  positive := Matrix.posSemidef_conjTranspose_mul_self _
  trace_one := coefficient_gram_trace ψ

/-- An actual contraction maps the canonical purification coefficients to the given coefficients. -/
theorem exists_coefficient_contraction (ψ : UnitPureInput r n) :
    ∃ A : Matrix (Fin r) (Fin n) ℂ, ‖A‖ ≤ 1 ∧
      coefficientMatrix ψ = A * CFC.sqrt (inputDensity ψ).matrix := by
  let S := CFC.sqrt (inputDensity ψ).matrix
  have hS : S.IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hSS : S * Sᴴ = (coefficientMatrix ψ)ᴴ * coefficientMatrix ψ := by
    rw [hS.eq]
    exact CFC.sqrt_mul_sqrt_self _ (inputDensity ψ).positive.nonneg
  have hdom : ((1 : ℝ) • (S * Sᴴ) - (coefficientMatrix ψ)ᴴ * ((coefficientMatrix ψ)ᴴ)ᴴ).PosSemidef := by
    rw [one_smul, hSS, Matrix.conjTranspose_conjTranspose, sub_self]
    exact Matrix.PosSemidef.zero
  obtain ⟨D, hD, hn⟩ := Factorization.matrix_factorization (coefficientMatrix ψ)ᴴ S (by norm_num : (0 : ℝ) ≤ 1) hdom
  refine ⟨Dᴴ, by simpa only [Matrix.l2_opNorm_conjTranspose, Real.sqrt_one] using hn, ?_⟩
  have ht := congrArg Matrix.conjTranspose hD
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, hS.eq] using ht

/-- The contraction completion dominates the desired local Kraus action on every PSD joint input. -/
theorem reference_channel_dominates (A : Matrix (Fin s) (Fin r) ℂ) (hA : ‖A‖ ≤ 1) (z : Fin s)
    (X : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ) (hX : X.PosSemidef) :
    (((KrausRecovery.channel A hA z).tensor (KrausChannel.identity n)).apply
      (Matrix.reindex finProdFinEquiv finProdFinEquiv X) -
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((A ⊗ₖ (1 : Operator n)) * X * (A ⊗ₖ (1 : Operator n))ᴴ)).PosSemidef := by
  rw [tensor_apply_reindex]
  simp only [KrausChannel.identity, Fin.sum_univ_one]
  change (Matrix.reindex finProdFinEquiv finProdFinEquiv
    (∑ i : Fin (1 + r),
      ((KrausRecovery.channel A hA z).kraus i ⊗ₖ (1 : Operator n)) * X *
        ((KrausRecovery.channel A hA z).kraus i ⊗ₖ (1 : Operator n))ᴴ) -
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((A ⊗ₖ (1 : Operator n)) * X * (A ⊗ₖ (1 : Operator n))ᴴ)).PosSemidef
  rw [Fin.sum_univ_add]
  simp only [KrausRecovery.channel, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_one]
  change (reindexHom finProdFinEquiv (_ + _) - reindexHom finProdFinEquiv _).PosSemidef
  rw [map_add, add_sub_cancel_left]
  have hsum : (∑ i : Fin r,
      (KrausRecovery.rowKraus (CFC.sqrt (KrausRecovery.defect A)) z i ⊗ₖ (1 : Operator n)) * X *
      (KrausRecovery.rowKraus (CFC.sqrt (KrausRecovery.defect A)) z i ⊗ₖ (1 : Operator n))ᴴ).PosSemidef := by
    apply Finset.sum_induction
    · intro B C hB hC
      exact hB.add hC
    · exact Matrix.PosSemidef.zero
    · intro i _
      exact hX.mul_mul_conjTranspose_same _
  exact hsum.submatrix finProdFinEquiv.symm

/-- Applying the reference contraction to a pure vector is ordinary left matrix multiplication. -/
theorem reference_conjugate_pure (A : Matrix (Fin s) (Fin r) ℂ)
    (φ : UnitPureInput r n) (ψ : UnitPureInput s n)
    (h : coefficientMatrix ψ = A * coefficientMatrix φ) :
    (A ⊗ₖ (1 : Operator n)) * pureMatrix φ.val * (A ⊗ₖ (1 : Operator n))ᴴ = pureMatrix ψ.val := by
  rw [conjugate_pureMatrix]
  congr 1
  ext ⟨i,j⟩
  have he := congrFun (congrFun h i) j
  simpa [coefficientMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, Matrix.mul_apply] using he.symm

/-- A trace-preserving completion is exact on a pure state whose norm the contraction preserves. -/
theorem reference_channel_recovers_pure (A : Matrix (Fin s) (Fin r) ℂ) (hA : ‖A‖ ≤ 1) (z : Fin s)
    (φ : UnitPureInput r n) (ψ : UnitPureInput s n)
    (h : coefficientMatrix ψ = A * coefficientMatrix φ) :
    ((KrausRecovery.channel A hA z).tensor (KrausChannel.identity n)).onState (pureInputState φ) =
      pureInputState ψ := by
  apply state_eq_of_matrix_eq
  apply KrausRecovery.eq_of_domination_trace_eq
  · have hp := reference_channel_dominates A hA z (pureMatrix φ.val) (pureMatrix_positive φ.val)
    rw [reference_conjugate_pure A φ ψ h] at hp
    exact hp
  · exact (((KrausRecovery.channel A hA z).tensor (KrausChannel.identity n)).onState
      (pureInputState φ)).trace_one.trans (pureInputState ψ).trace_one.symm

/-- Every pure input with any finite reference is recovered by an actual channel
on the canonical input-sized reference, independently of the tested channel. -/
theorem exists_reference_recovery (ψ : UnitPureInput r n) :
    ∃ Γ : KrausChannel n r,
      (Γ.tensor (KrausChannel.identity n)).onState
        (pureInputState (TestingPrimal.densityInput (inputDensity ψ))) = pureInputState ψ := by
  obtain ⟨A, hA, hcoeff⟩ := exists_coefficient_contraction ψ
  have hrn : 0 < r * n := MatrixOperatorBridge.state_dimension_pos (pureInputState ψ)
  have hr : 0 < r := Nat.pos_of_mul_pos_right hrn
  exact ⟨KrausRecovery.channel A hA ⟨0, hr⟩,
    reference_channel_recovers_pure A hA ⟨0, hr⟩ _ ψ hcoeff⟩

/-- The same reference recovery channel works for both output hypotheses. -/
theorem exists_output_reference_recovery (ψ : UnitPureInput r n) :
    ∃ Γ : KrausChannel n r, ∀ Φ : KrausChannel n m,
      (Γ.tensor (KrausChannel.identity m)).onState
        (pureOutput Φ (TestingPrimal.densityInput (inputDensity ψ))) = pureOutput Φ ψ := by
  obtain ⟨Γ, hΓ⟩ := exists_reference_recovery ψ
  refine ⟨Γ, ?_⟩
  intro Φ
  have h := reference_recovery_output Γ Φ
    (pureInputState (TestingPrimal.densityInput (inputDensity ψ)))
  rw [hΓ] at h
  have hp (φ : UnitPureInput r n) : outputState Φ r (pureInputState φ) = pureOutput Φ φ :=
    state_eq_of_matrix_eq _ _ (outputState_pureInputState_matrix Φ φ)
  have hp' (φ : UnitPureInput n n) : outputState Φ n (pureInputState φ) = pureOutput Φ φ :=
    state_eq_of_matrix_eq _ _ (outputState_pureInputState_matrix Φ φ)
  rwa [hp, hp'] at h

end QuantumChannelStein.PureReferenceRecovery
