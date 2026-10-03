import QuantumChannelStein.TestingSDP
import QuantumChannelStein.Factorization
import QuantumChannelStein.TensorPower
import QuantumChannelStein.ChannelEntropyChoi

/-!
# Operational correspondence for the channel-testing primal SDP

Equation (4.2) of arXiv:2609.27196v1 is proved for actual channel outputs
and binary effects. Every pure input/test gives feasible density/test
matrices, and every feasible pair is realized by a pure input and effect.
The converse uses Douglas factorization and includes singular densities.
Compact primal attainment supplies a genuine maximum on both sides.

This file does not claim the strong-duality equality (4.3).
-/
noncomputable section
namespace QuantumChannelStein.TestingPrimal
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open Matrix WithLp ChannelEntropy TestingSDP

variable {n m : ℕ}

/-- Coefficients of a reference-input pure vector as a rectangular array. -/
def coefficientVector (S : Operator n) : EuclideanSpace ℂ (Fin n × Fin n) :=
  toLp 2 (fun p => S p.1 p.2)

/-- The coefficient matrix of an actual pure channel input. -/
def coefficientMatrix (ψ : UnitPureInput n n) : Operator n :=
  fun i j => ψ.val (i, j)

@[simp] theorem coefficientVector_coefficientMatrix (ψ : UnitPureInput n n) :
    coefficientVector (coefficientMatrix ψ) = ψ.val := by
  ext p
  rfl

/-- Hilbert normalization of the vector is trace normalization of its Gram matrix. -/
theorem coefficientVector_norm_sq (S : Operator n) :
    ‖coefficientVector S‖ ^ 2 = (Sᴴ * S).trace.re := by
  rw [Matrix.trace_mul_comm]
  simp [EuclideanSpace.norm_sq_eq, coefficientVector, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, ← Complex.normSq_eq_norm_sq,
    Complex.mul_conj]

/-- The input Gram matrix is an actual density operator. -/
def inputDensity (ψ : UnitPureInput n n) : State n where
  matrix := (coefficientMatrix ψ)ᴴ * coefficientMatrix ψ
  positive := Matrix.posSemidef_conjTranspose_mul_self _
  trace_one := by
    apply Complex.ext
    · rw [← coefficientVector_norm_sq, coefficientVector_coefficientMatrix, ψ.property]
      norm_num
    · exact (Complex.nonneg_iff.mp
        (Matrix.posSemidef_conjTranspose_mul_self (coefficientMatrix ψ)).trace_nonneg).2.symm

/-- The actual amplified pure output is the Choi operator conjugated by
the input's coefficient matrix on its reference coordinate. -/
theorem amplify_coefficientVector (Φ : KrausChannel n m) (S : Operator n) :
    Φ.amplify n (pureMatrix (coefficientVector S)) =
      (S ⊗ₖ (1 : Operator m)) * Φ.choi * (S ⊗ₖ (1 : Operator m))ᴴ := by
  ext ⟨r, a⟩ ⟨s, b⟩
  rw [KrausChannel.amplify_block]
  change Φ.toLinearMap (fun i j => pureMatrix (coefficientVector S) (r, i) (s, j)) a b = _
  rw [MatrixMap.apply_eq_sum_choi]
  simp only [pureMatrix, coefficientVector, ofLp_toLp, Matrix.vecMulVec_apply,
    Pi.star_apply, MatrixMap.choi_toLinearMap]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.sum_mul, apply_ite]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The same Choi conjugation formula for every allowed unit input. -/
theorem amplify_pureInput (Φ : KrausChannel n m) (ψ : UnitPureInput n n) :
    Φ.amplify n (pureMatrix ψ.val) =
      (coefficientMatrix ψ ⊗ₖ (1 : Operator m)) * Φ.choi *
        (coefficientMatrix ψ ⊗ₖ (1 : Operator m))ᴴ := by
  rw [← coefficientVector_coefficientMatrix ψ]
  exact amplify_coefficientVector Φ (coefficientMatrix ψ)


/-- The same physical effect in unflattened reference/output coordinates. -/
def rawEffect (T : Effect (n * m)) : BipartiteOperator n m :=
  Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm T.matrix

theorem rawEffect_positive (T : Effect (n * m)) : (rawEffect T).PosSemidef :=
  T.positive.submatrix finProdFinEquiv

theorem rawEffect_complement_positive (T : Effect (n * m)) :
    (1 - rawEffect T).PosSemidef := by
  have h := T.complement_positive.submatrix finProdFinEquiv
  change (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv.symm finProdFinEquiv.symm
    (1 - T.matrix)).PosSemidef at h
  rw [map_sub, Matrix.reindexLinearEquiv_one] at h
  exact h

/-- Identity extension commutes with the coefficient Gram matrix. -/
theorem reference_gram (S : Operator n) :
    (S ⊗ₖ (1 : Operator m))ᴴ * (S ⊗ₖ (1 : Operator m)) =
      (Sᴴ * S) ⊗ₖ (1 : Operator m) := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Every actual pure input and binary effect give feasible primal matrices. -/
def pureTestPrimal (ψ : UnitPureInput n n) (T : Effect (n * m)) : PrimalFeasible n m where
  omega := inputDensity ψ
  Q := (coefficientMatrix ψ ⊗ₖ (1 : Operator m))ᴴ * rawEffect T *
    (coefficientMatrix ψ ⊗ₖ (1 : Operator m))
  positive := (rawEffect_positive T).conjTranspose_mul_mul_same _
  dominated := by
    have h := (rawEffect_complement_positive T).conjTranspose_mul_mul_same
      (coefficientMatrix ψ ⊗ₖ (1 : Operator m))
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, reference_gram] at h
    exact h

/-- Undoing output flattening preserves the actual test probability. -/
theorem pureOutput_probability_raw (Φ : KrausChannel n m) (ψ : UnitPureInput n n)
    (T : Effect (n * m)) :
    T.probability (pureOutput Φ ψ) = (rawEffect T * Φ.amplify n (pureMatrix ψ.val)).trace.re := by
  have hT : T.matrix = Matrix.reindex finProdFinEquiv finProdFinEquiv (rawEffect T) := by
    ext i j
    change T.matrix i j = T.matrix
      (finProdFinEquiv (finProdFinEquiv.symm i : Fin n × Fin m))
      (finProdFinEquiv (finProdFinEquiv.symm j : Fin n × Fin m))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change (T.matrix * Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Φ.amplify n (pureMatrix ψ.val))).trace.re = _
  rw [hT]
  change ((Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (rawEffect T)) *
    (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
      (Φ.amplify n (pureMatrix ψ.val)))).trace.re = _
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_apply, trace_reindex_equiv]

/-- Cyclic trace is the exact adjoint relation for pulling an effect backward. -/
theorem trace_pullback {ι : Type*} [Fintype ι] (A R T : Matrix ι ι ℂ) :
    (A * (Rᴴ * T * R)).trace = (T * (R * A * Rᴴ)).trace := by
  calc
    (A * (Rᴴ * T * R)).trace = ((A * (Rᴴ * T)) * R).trace := by
      simp only [Matrix.mul_assoc]
    _ = (R * (A * (Rᴴ * T))).trace := Matrix.trace_mul_comm _ _
    _ = ((R * A * Rᴴ) * T).trace := by simp only [Matrix.mul_assoc]
    _ = (T * (R * A * Rᴴ)).trace := Matrix.trace_mul_comm _ _

/-- The Hermitian Choi difference used by the channel-testing SDP. -/
def channelDifference (Φ Ψ : KrausChannel n m) (t : ℝ) : BipartiteOperator n m :=
  Φ.choi - t • Ψ.choi

/-- The actual difference of two Born acceptance probabilities. -/
def pureScore (Φ Ψ : KrausChannel n m) (t : ℝ) (ψ : UnitPureInput n n)
    (T : Effect (n * m)) : ℝ :=
  T.probability (pureOutput Φ ψ) - t * T.probability (pureOutput Ψ ψ)

/-- Forward operational/primal objective identity, with no implicit
transpose convention or pure-input isometry assumption. -/
theorem pureTestPrimal_value (Φ Ψ : KrausChannel n m) (t : ℝ)
    (ψ : UnitPureInput n n) (T : Effect (n * m)) :
    (pureTestPrimal ψ T).value (channelDifference Φ Ψ t) = pureScore Φ Ψ t ψ T := by
  change ((Φ.choi - t • Ψ.choi) *
    ((coefficientMatrix ψ ⊗ₖ (1 : Operator m))ᴴ * rawEffect T *
      (coefficientMatrix ψ ⊗ₖ (1 : Operator m)))).trace.re = _
  rw [trace_pullback]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← amplify_pureInput, ← amplify_pureInput]
  rw [← pureOutput_probability_raw, ← pureOutput_probability_raw]
  rfl


/-- The canonical pure input associated with a density matrix, including
singular density matrices. -/
def densityInput (omega : State n) : UnitPureInput n n :=
  ⟨coefficientVector (CFC.sqrt omega.matrix), by
    have h := coefficientVector_norm_sq (CFC.sqrt omega.matrix)
    have hs : (CFC.sqrt omega.matrix).IsHermitian := (CFC.sqrt_nonneg omega.matrix).posSemidef.isHermitian
    rw [hs.eq, CFC.sqrt_mul_sqrt_self omega.matrix omega.positive.nonneg,
      omega.trace_one, Complex.one_re] at h
    nlinarith [norm_nonneg (coefficientVector (CFC.sqrt omega.matrix))]⟩

@[simp] theorem coefficientMatrix_densityInput (omega : State n) :
    coefficientMatrix (densityInput omega) = CFC.sqrt omega.matrix := rfl

/-- Every feasible primal matrix is the pullback of an actual effect for
the canonical pure input. Douglas factorization handles the kernel of omega. -/
theorem exists_effect_realizing_primal (P : PrimalFeasible n m) :
    ∃ T : Effect (n * m), (pureTestPrimal (densityInput P.omega) T).Q = P.Q := by
  let F : BipartiteOperator n m := CFC.sqrt P.Q
  let G : BipartiteOperator n m := CFC.sqrt P.omega.matrix ⊗ₖ (1 : Operator m)
  have hs : (CFC.sqrt P.omega.matrix).IsHermitian :=
    (CFC.sqrt_nonneg P.omega.matrix).posSemidef.isHermitian
  have hF : F * Fᴴ = P.Q := by
    dsimp [F]
    rw [(CFC.sqrt_nonneg P.Q).posSemidef.isHermitian.eq,
      CFC.sqrt_mul_sqrt_self P.Q P.positive.nonneg]
  have hG : G * Gᴴ = P.omega.matrix ⊗ₖ (1 : Operator m) := by
    dsimp [G]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hs.eq,
      ← Matrix.mul_kronecker_mul, CFC.sqrt_mul_sqrt_self P.omega.matrix P.omega.positive.nonneg,
      Matrix.one_mul]
  have hGh : Gᴴ = G := by
    dsimp [G]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hs.eq]
  have hdom : ((1 : ℝ) • (G * Gᴴ) - F * Fᴴ).PosSemidef := by
    simpa only [one_smul, hF, hG] using P.dominated
  obtain ⟨D, hD, hDn⟩ := Factorization.matrix_factorization F G zero_le_one hdom
  have hDn' : ‖D‖ ≤ 1 := by simpa using hDn
  let M : BipartiteOperator n m := D * Dᴴ
  have hM : M.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _
  have hMn : ‖M‖ ≤ 1 := by
    calc
      ‖M‖ ≤ ‖D‖ * ‖Dᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul hDn' (by simpa only [Matrix.l2_opNorm_conjTranspose] using hDn')
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  let T : Effect (n * m) := {
    matrix := Matrix.reindex finProdFinEquiv finProdFinEquiv M
    positive := hM.submatrix finProdFinEquiv.symm
    complement_positive := by
      letI : CStarAlgebra (Operator (n * m)) := CStarAlgebra.mk
      apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
        (hM.submatrix finProdFinEquiv.symm).nonneg).mp
      change ‖Matrix.reindex finProdFinEquiv finProdFinEquiv M‖ ≤ 1
      rw [TensorPower.norm_reindex]
      exact hMn }
  have hraw : rawEffect T = M := by
    ext i j
    simp [T, rawEffect, Matrix.reindex_apply]
  refine ⟨T, ?_⟩
  change Gᴴ * rawEffect T * G = P.Q
  rw [hraw, hGh, ← hF, hD, Matrix.conjTranspose_mul, hGh]
  simp only [M, Matrix.mul_assoc]

/-- Converse objective identity: no feasible primal objective is fictitious. -/
theorem exists_pure_test_of_primal (Φ Ψ : KrausChannel n m) (t : ℝ)
    (P : PrimalFeasible n m) :
    ∃ ψ : UnitPureInput n n, ∃ T : Effect (n * m),
      pureScore Φ Ψ t ψ T = P.value (channelDifference Φ Ψ t) := by
  obtain ⟨T, hT⟩ := exists_effect_realizing_primal P
  refine ⟨densityInput P.omega, T, ?_⟩
  rw [← pureTestPrimal_value]
  change ((channelDifference Φ Ψ t) * (pureTestPrimal (densityInput P.omega) T).Q).trace.re = _
  rw [hT]
  rfl

/-- The channel hockey-stick quantity defined operationally by all allowed
fixed-reference pure inputs and binary effects. -/
def channelHockeyStick (Φ Ψ : KrausChannel n m) (t : ℝ) : ℝ :=
  sSup (Set.range (fun x : UnitPureInput n n × Effect (n * m) => pureScore Φ Ψ t x.1 x.2))

/-- The operational and SDP formulations have exactly the same attainable
objective values, even when the primal density matrix is singular. -/
theorem operational_primal_value_set (Φ Ψ : KrausChannel n m) (t : ℝ) :
    Set.range (fun x : UnitPureInput n n × Effect (n * m) => pureScore Φ Ψ t x.1 x.2) =
      Set.range (fun P : PrimalFeasible n m => P.value (channelDifference Φ Ψ t)) := by
  ext v
  constructor
  · rintro ⟨⟨ψ, T⟩, rfl⟩
    exact ⟨pureTestPrimal ψ T, pureTestPrimal_value Φ Ψ t ψ T⟩
  · rintro ⟨P, rfl⟩
    obtain ⟨ψ, T, h⟩ := exists_pure_test_of_primal Φ Ψ t P
    exact ⟨(ψ, T), h⟩

/-- Equation (4.2), expressed as equality of operational and primal suprema.
Primal compact attainment upgrades this to the paper's maximum. -/
theorem channelHockeyStick_eq_primalSup (Φ Ψ : KrausChannel n m) (t : ℝ) :
    channelHockeyStick Φ Ψ t =
      sSup (Set.range (fun P : PrimalFeasible n m => P.value (channelDifference Φ Ψ t))) := by
  unfold channelHockeyStick
  rw [operational_primal_value_set]


/-- Compact primal attainment and the operational value-set correspondence
turn equation (4.2) into a maximum, rather than only a supremum identity. -/
theorem exists_primal_maximizer_eq_channelHockeyStick (Φ Ψ : KrausChannel n m)
    (hn : 0 < n) (t : ℝ) :
    ∃ P : PrimalFeasible n m, channelHockeyStick Φ Ψ t = P.value (channelDifference Φ Ψ t) ∧
      ∀ P' : PrimalFeasible n m, P'.value (channelDifference Φ Ψ t) ≤ P.value (channelDifference Φ Ψ t) := by
  obtain ⟨P, hP⟩ := TestingSDP.exists_primal_maximizer
    (inputDensity (maximallyEntangledInput hn)) (channelDifference Φ Ψ t)
  refine ⟨P, ?_, hP⟩
  rw [channelHockeyStick_eq_primalSup]
  have hb : BddAbove (Set.range (fun P' : PrimalFeasible n m =>
      P'.value (channelDifference Φ Ψ t))) := by
    refine ⟨P.value (channelDifference Φ Ψ t), ?_⟩
    rintro y ⟨P', rfl⟩
    exact hP P'
  apply le_antisymm
  · have hnempty : (Set.range (fun P' : PrimalFeasible n m =>
        P'.value (channelDifference Φ Ψ t))).Nonempty :=
      ⟨P.value (channelDifference Φ Ψ t), ⟨P, rfl⟩⟩
    apply csSup_le hnempty
    rintro y ⟨P', rfl⟩
    exact hP P'
  · exact le_csSup hb ⟨P, rfl⟩

/-- Every operational score is bounded by its hockey-stick supremum. -/
theorem pureScore_le_channelHockeyStick (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (t : ℝ) (ψ : UnitPureInput n n) (T : Effect (n * m)) :
    pureScore Φ Ψ t ψ T ≤ channelHockeyStick Φ Ψ t := by
  obtain ⟨P, hvalue, hP⟩ := exists_primal_maximizer_eq_channelHockeyStick Φ Ψ hn t
  rw [hvalue]
  simpa only [pureTestPrimal_value] using hP (pureTestPrimal ψ T)

/-- The operational hockey-stick supremum is attained by a real input and effect. -/
theorem exists_pure_maximizer (Φ Ψ : KrausChannel n m) (hn : 0 < n) (t : ℝ) :
    ∃ ψ : UnitPureInput n n, ∃ T : Effect (n * m),
      pureScore Φ Ψ t ψ T = channelHockeyStick Φ Ψ t := by
  obtain ⟨P, hvalue, _⟩ := exists_primal_maximizer_eq_channelHockeyStick Φ Ψ hn t
  obtain ⟨ψ, T, hscore⟩ := exists_pure_test_of_primal Φ Ψ t P
  exact ⟨ψ, T, hscore.trans hvalue.symm⟩

/-- Rejecting every outcome gives zero hockey-stick score. -/
def rejectAll (d : ℕ) : Effect d where
  matrix := 0
  positive := Matrix.PosSemidef.zero
  complement_positive := by simpa only [sub_zero] using (Matrix.PosSemidef.one : (1 : Operator d).PosSemidef)

@[simp] theorem pureScore_rejectAll (Φ Ψ : KrausChannel n m) (t : ℝ)
    (ψ : UnitPureInput n n) : pureScore Φ Ψ t ψ (rejectAll _) = 0 := by
  simp [pureScore, rejectAll, Effect.probability]

/-- Operational nonnegativity follows from the zero test. -/
theorem channelHockeyStick_nonneg (Φ Ψ : KrausChannel n m) (hn : 0 < n) (t : ℝ) :
    0 ≤ channelHockeyStick Φ Ψ t := by
  simpa only [pureScore_rejectAll] using
    pureScore_le_channelHockeyStick Φ Ψ hn t (maximallyEntangledInput hn) (rejectAll _)

/-- For nonnegative threshold t, every actual score is at most one. -/
theorem pureScore_le_one (Φ Ψ : KrausChannel n m) {t : ℝ} (ht : 0 ≤ t)
    (ψ : UnitPureInput n n) (T : Effect (n * m)) : pureScore Φ Ψ t ψ T ≤ 1 := by
  have hp := T.probability_le_one (pureOutput Φ ψ)
  have hq := mul_nonneg ht (T.probability_nonneg (pureOutput Ψ ψ))
  unfold pureScore
  linarith only [hp, hq]

/-- The actual channel hockey-stick quantity lies in [0,1] for t≥0. -/
theorem channelHockeyStick_le_one (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) : channelHockeyStick Φ Ψ t ≤ 1 := by
  obtain ⟨ψ, T, h⟩ := exists_pure_maximizer Φ Ψ hn t
  rw [← h]
  exact pureScore_le_one Φ Ψ ht ψ T

/-- Any concrete feasible dual matrix bounds all operational input/test pairs. -/
theorem channelHockeyStick_le_dual (Φ Ψ : KrausChannel n m) (hn : 0 < n) (t : ℝ)
    (D : DualFeasible (channelDifference Φ Ψ t)) : channelHockeyStick Φ Ψ t ≤ D.value := by
  obtain ⟨P, h, _⟩ := exists_primal_maximizer_eq_channelHockeyStick Φ Ψ hn t
  rw [h]
  exact TestingSDP.weak_duality P D

end QuantumChannelStein.TestingPrimal
