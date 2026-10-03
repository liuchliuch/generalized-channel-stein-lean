import QuantumChannelStein.ReferenceAcceptance

/-!
# Explicit purification and mixed-input acceptance amplitudes

A positive matrix is purified using the columns of its positive square root.
The tested marginal identity is established by finite matrix sums, so the
mixed-input acceptance inequality is reduced to the checked pure-input one.
-/
set_option maxHeartbeats 1200000
noncomputable section
namespace QuantumChannelStein.Purification
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix WithLp
open ReferenceAcceptance

variable {p n o e f : Type*} [Fintype p] [Fintype n] [Fintype o]
  [Fintype e] [Fintype f]

/-- The columns of a matrix viewed as a purification vector. -/
def vector (S : Matrix n p ℂ) : EuclideanSpace ℂ (p × n) :=
  toLp 2 (fun q => S q.2 q.1)

/-- Tracing out the column index of a purification recovers the Gram matrix. -/
theorem vector_marginal (S : Matrix n p ℂ) (i j : n) :
    ∑ k, pureMatrix (vector S) (k, i) (k, j) = (S * Sᴴ) i j := by
  simp [pureMatrix, vector, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec]

/-- The purification has squared norm equal to the trace of its Gram matrix. -/
theorem vector_norm_sq (S : Matrix n p ℂ) :
    ‖vector S‖ ^ 2 = (S * Sᴴ).trace.re := by
  rw [← trace_pureMatrix_re]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [vector_marginal]

/-- Reassociate a purified output, with the purifying index first. -/
def output (S : Matrix (o × e) p ℂ) : EuclideanSpace ℂ ((p × o) × e) :=
  toLp 2 (fun q => S (q.1.2, q.2) q.1.1)

variable [DecidableEq p] [DecidableEq n] [DecidableEq o]
  [DecidableEq e] [DecidableEq f]

omit [DecidableEq o] [DecidableEq e] in
/-- The reference-extended dilation acts on each column of the purification. -/
theorem dilation_vector (U : Matrix (o × e) n ℂ) (S : Matrix n p ℂ) :
    TensorNorm.matrixMap (dilation U) (vector S) = output (U * S) := by
  ext ⟨⟨k, i⟩, j⟩
  simp [TensorNorm.matrixMap_apply, dilation, Matrix.mulVec, dotProduct,
    Matrix.one_apply, Fintype.sum_prod_type, vector, output, Matrix.mul_apply]

omit [DecidableEq o] [DecidableEq e] in
/-- Testing while ignoring the purifying register preserves the acceptance
weight of the mixed state exactly. -/
theorem output_acceptance (T : Matrix o o ℂ) (S : Matrix (o × e) p ℂ) :
    acceptance ((1 : Matrix p p ℂ) ⊗ₖ T) (output S) =
      (T * traceEnvironment (S * Sᴴ)).trace.re := by
  unfold acceptance
  apply congrArg Complex.re
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, traceEnvironment,
    pureMatrix, output, ofLp_toLp, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.conjTranspose_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.mul_sum, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

/-- Identity extension of a positive test remains positive. -/
theorem one_kronecker_positive (T : Matrix o o ℂ) (hT : T.PosSemidef) :
    ((1 : Matrix p p ℂ) ⊗ₖ T).PosSemidef := by
  have hs : (CFC.sqrt T).PosSemidef := (CFC.sqrt_nonneg T).posSemidef
  have h : ((1 : Matrix p p ℂ) ⊗ₖ T) =
      (((1 : Matrix p p ℂ) ⊗ₖ CFC.sqrt T)ᴴ *
        ((1 : Matrix p p ℂ) ⊗ₖ CFC.sqrt T)) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      hs.isHermitian.eq, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      CFC.sqrt_mul_sqrt_self T hT.nonneg]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Ignoring the purifying register also preserves the upper bound on a test. -/
theorem one_kronecker_complement_positive (T : Matrix o o ℂ)
    (hTc : (1 - T).PosSemidef) :
    (1 - ((1 : Matrix p p ℂ) ⊗ₖ T)).PosSemidef := by
  have h := one_kronecker_positive (p := p) (1 - T) hTc
  convert h using 1
  ext i j
  by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
    simp [Matrix.one_apply, mul_sub, Prod.ext_iff, h₁, h₂]

/-- Mixed-state Born weight obtained by applying the dilation and discarding
its environment. -/
def mixedAcceptance (T : Matrix o o ℂ) (U : Matrix (o × e) n ℂ)
    (ρ : Matrix n n ℂ) : ℝ :=
  (T * traceEnvironment (U * ρ * Uᴴ)).trace.re

omit [DecidableEq o] [DecidableEq e] in
/-- The explicit purification yields the same mixed-state Born weight after
any dilation and test. -/
theorem purified_acceptance (T : Matrix o o ℂ) (U : Matrix (o × e) n ℂ)
    (S : Matrix n p ℂ) :
    acceptance ((1 : Matrix p p ℂ) ⊗ₖ T)
      (TensorNorm.matrixMap (dilation U) (vector S)) =
        mixedAcceptance T U (S * Sᴴ) := by
  rw [dilation_vector, output_acceptance]
  simp only [mixedAcceptance, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The square-root matrix supplies an explicit purification of every density
matrix. In particular, a purification is constructed rather than assumed. -/
theorem sqrt_purification (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) :
    CFC.sqrt ρ * (CFC.sqrt ρ)ᴴ = ρ ∧ ‖vector (CFC.sqrt ρ)‖ = 1 := by
  have hs : (CFC.sqrt ρ).PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hgram : CFC.sqrt ρ * (CFC.sqrt ρ)ᴴ = ρ := by
    rw [hs.isHermitian.eq, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
  refine ⟨hgram, ?_⟩
  have hn := vector_norm_sq (CFC.sqrt ρ)
  rw [hgram, htr] at hn
  simp only [Complex.one_re] at hn
  nlinarith [norm_nonneg (vector (CFC.sqrt ρ))]

/-- Mixed-input acceptance amplitudes, with the original dilation error. The
proof purifies the density matrix explicitly and proves marginal preservation. -/
theorem mixed_acceptance_le (T : Matrix o o ℂ)
    (hT : T.PosSemidef) (hTc : (1 - T).PosSemidef)
    (UN : Matrix (o × e) n ℂ) (UM : Matrix (o × f) n ℂ) (C : Matrix e f ℂ)
    (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    Real.sqrt (mixedAcceptance T UN ρ) ≤
      ‖C‖ * Real.sqrt (mixedAcceptance T UM ρ) +
        ‖UN - ((1 : Matrix o o ℂ) ⊗ₖ C) * UM‖ := by
  obtain ⟨hgram, hnorm⟩ := sqrt_purification ρ hρ htr
  have h := pure_reference_acceptance_le ((1 : Matrix n n ℂ) ⊗ₖ T)
    (one_kronecker_positive T hT) (one_kronecker_complement_positive T hTc)
    UN UM C (vector (CFC.sqrt ρ)) hnorm.le
  simpa only [purified_acceptance, hgram] using h

/-- Full matrix form of Lemma 3.4 for an arbitrary finite reference and mixed
reference-assisted input. The binary test is joint on reference and output;
the error norm is on the original, unextended dilations. -/
theorem mixed_reference_acceptance_le
    {r a b : Type*} [Fintype r] [Fintype a] [Fintype b]
    [DecidableEq r] [DecidableEq a] [DecidableEq b]
    (T : Matrix (r × b) (r × b) ℂ)
    (hT : T.PosSemidef) (hTc : (1 - T).PosSemidef)
    (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ) (C : Matrix e f ℂ)
    (ρ : Matrix (r × a) (r × a) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    Real.sqrt (mixedAcceptance T (dilation VN) ρ) ≤
      ‖C‖ * Real.sqrt (mixedAcceptance T (dilation VM) ρ) +
        ‖VN - ((1 : Matrix b b ℂ) ⊗ₖ C) * VM‖ := by
  apply (mixed_acceptance_le T hT hTc (dilation VN) (dilation VM) C ρ hρ htr).trans
  have herr : ‖dilation (r := r) VN -
      ((1 : Matrix (r × b) (r × b) ℂ) ⊗ₖ C) * dilation VM‖ ≤
      ‖VN - ((1 : Matrix b b ℂ) ⊗ₖ C) * VM‖ := by
    rw [← dilation_environment, ← dilation_sub]
    exact dilation_opNorm_le _
  linarith only [herr]

/-- The reference-extended canonical Stinespring dilation implements exactly
the channel's existing Kraus-amplification operation. -/
theorem stinespring_reference_marginal {a b r : ℕ} (Φ : KrausChannel a b)
    (ρ : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    traceEnvironment (dilation Φ.stinespring * ρ * (dilation Φ.stinespring)ᴴ) =
      Φ.amplify r ρ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [traceEnvironment, dilation, KrausChannel.stinespring, KrausChannel.amplify,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type]

/-- Lemma 3.4 for the actual acceptance probabilities of any two concrete
Kraus channels, arbitrary reference dimension, arbitrary mixed input, and
arbitrary joint binary test. -/
theorem kraus_reference_acceptance_le {a b r : ℕ}
    (Φ Ψ : KrausChannel a b)
    (T : Matrix (Fin r × Fin b) (Fin r × Fin b) ℂ)
    (hT : T.PosSemidef) (hTc : (1 - T).PosSemidef)
    (C : Matrix (Fin Φ.rank) (Fin Ψ.rank) ℂ)
    (ρ : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    Real.sqrt ((T * Φ.amplify r ρ).trace.re) ≤
      ‖C‖ * Real.sqrt ((T * Ψ.amplify r ρ).trace.re) +
        ‖Φ.stinespring - ((1 : Operator b) ⊗ₖ C) * Ψ.stinespring‖ := by
  have h := mixed_reference_acceptance_le T hT hTc Φ.stinespring Ψ.stinespring
    C ρ hρ htr
  simpa only [mixedAcceptance, stinespring_reference_marginal] using h

omit [DecidableEq e] in
/-- The reference-extended dilation acts on each reference block by the
original dilation's channel. -/
theorem prescribed_dilation_block {r a b : Type*}
    [Fintype r] [Fintype a] [Fintype b]
    [DecidableEq r] [DecidableEq a] [DecidableEq b]
    (V : Matrix (b × e) a ℂ)
    (ρ : Matrix (r × a) (r × a) ℂ) (i k : r) (j l : b) :
    traceEnvironment (dilation V * ρ * (dilation V)ᴴ) (i, j) (k, l) =
      traceEnvironment (V * (Matrix.of (fun x y => ρ (i, x) (k, y))) * Vᴴ) j l := by
  simp [traceEnvironment, dilation, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type, apply_ite]

omit [DecidableEq e] in
/-- Any prescribed Stinespring representation remains a representation after
reference extension, without assuming its reference-assisted formula. -/
theorem prescribed_stinespring_reference_marginal {a b r : ℕ}
    (Φ : KrausChannel a b) (V : Matrix (Fin b × e) (Fin a) ℂ)
    (hV : ∀ X : Operator a, traceEnvironment (V * X * Vᴴ) = Φ.apply X)
    (ρ : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
    traceEnvironment (dilation V * ρ * (dilation V)ᴴ) = Φ.amplify r ρ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [prescribed_dilation_block, hV, KrausChannel.amplify_block]
  rfl

/-- **Lemma 3.4 (Acceptance amplitudes).** For arbitrary prescribed Stinespring
representations of two channels, every reference-assisted mixed state and
joint binary test obey the claimed inequality. The defining representation
identities are the only assumptions on the dilations needed by the proof;
in particular, the estimate holds for the Stinespring isometries in the paper. -/
theorem lemma_3_4 {a b r : ℕ}
    (Φ Ψ : KrausChannel a b)
    (VN : Matrix (Fin b × e) (Fin a) ℂ)
    (VM : Matrix (Fin b × f) (Fin a) ℂ)
    (hVN : ∀ X : Operator a, traceEnvironment (VN * X * VNᴴ) = Φ.apply X)
    (hVM : ∀ X : Operator a, traceEnvironment (VM * X * VMᴴ) = Ψ.apply X)
    (C : Matrix e f ℂ)
    (ρ : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (T : Matrix (Fin r × Fin b) (Fin r × Fin b) ℂ)
    (hT : T.PosSemidef) (hTc : (1 - T).PosSemidef) :
    Real.sqrt ((T * Φ.amplify r ρ).trace.re) ≤
      ‖C‖ * Real.sqrt ((T * Ψ.amplify r ρ).trace.re) +
        ‖VN - ((1 : Operator b) ⊗ₖ C) * VM‖ := by
  have h := mixed_reference_acceptance_le T hT hTc VN VM C ρ hρ htr
  simpa only [mixedAcceptance, prescribed_stinespring_reference_marginal Φ VN hVN,
    prescribed_stinespring_reference_marginal Ψ VM hVM] using h

end QuantumChannelStein.Purification
