import QuantumChannelStein.AdaptiveTesting
import QuantumChannelStein.ChannelEntropySuperadditive

/-! # Actual repeated-block pure inputs, state tests, and exact remainder padding -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ParallelBlockTests
open Matrix ChannelEntropy ChannelPowerReindex PerfectDiscrimination TensorPower
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b d d' : ℕ}

theorem state_one_unique (ρ σ : State 1) : ρ = σ := by
  apply State.eq_of_matrix_eq
  ext i j
  have hρ := ρ.trace_one
  have hσ := σ.trace_one
  fin_cases i
  fin_cases j
  simpa only [Matrix.trace, Matrix.diag, Fin.sum_univ_one] using hρ.trans hσ.symm

/-- Normalized pure inputs on two actual channel blocks, in the canonical total-use coordinates. -/
def combineInput (p q : ℕ) (ψ : UnitPureInput (a ^ p) (a ^ p))
    (φ : UnitPureInput (a ^ q) (a ^ q)) : UnitPureInput (a ^ (p + q)) (a ^ (p + q)) :=
  reindexInput (channelAddEquiv a p q) (productInput ψ φ)

/-- The corresponding explicit output-coordinate permutation. -/
def combineOutput (a b p q : ℕ) :
    Fin ((a ^ p * b ^ p) * (a ^ q * b ^ q)) ≃ Fin (a ^ (p + q) * b ^ (p + q)) :=
  (outputRegroup (a ^ p) (b ^ p) (a ^ q) (b ^ q)).trans
    (outputReindex (channelAddEquiv a p q) (channelAddEquiv b p q))

theorem pureOutput_combineInput (Φ : KrausChannel a b) (p q : ℕ)
    (ψ : UnitPureInput (a ^ p) (a ^ p)) (φ : UnitPureInput (a ^ q) (a ^ q)) :
    pureOutput (Φ.tensorPower (p + q)) (combineInput p q ψ φ) =
      ((pureOutput (Φ.tensorPower p) ψ).tensor (pureOutput (Φ.tensorPower q) φ)).reindex
        (combineOutput a b p q) := by
  rw [combineInput]
  rw [← pureOutput_congr _ _ (tensorPower_add_toLinearMap Φ p q)]
  rw [pureOutput_reindexChannel, pureOutput_productInput, State.reindex_trans]
  rfl

/-- Right-factor coordinate changes commute with the actual state tensor product. -/
theorem tensor_reindex_right (ρ : State d) (σ : State d') {e : ℕ} (f : Fin d' ≃ Fin e) :
    ρ.tensor (σ.reindex f) = (ρ.tensor σ).reindex (outputReindex (Equiv.refl _) f) := by
  apply State.eq_of_matrix_eq
  ext i j
  simp [State.tensor, State.reindex, outputReindex, Matrix.reindex_apply]

def statePowerJoin (d m : ℕ) : Fin (d * d ^ m) ≃ Fin (d ^ (m + 1)) :=
  finCongr (@Nat.pow_succ' d m).symm

/-- The existing genuine tensor state power has the expected normalized successor. -/
theorem statePower_succ (ρ : State d) (m : ℕ) :
    statePower ρ (m + 1) = (ρ.tensor (statePower ρ m)).reindex (statePowerJoin d m) := by
  apply State.eq_of_matrix_eq
  ext i j
  simp [statePower, State.tensor, State.reindex, statePowerJoin, channelIndexEquiv,
    Matrix.reindex_apply, tensorPower_succ, Equiv.prodCongr]

/-- Recursive block count, avoiding hidden dimension casts during construction. -/
def blocks (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => k + blocks k m

@[simp] theorem blocks_eq_mul (k m : ℕ) : blocks k m = k * m := by
  induction m with
  | zero => simp [blocks]
  | succ m ih => simp [blocks, ih, Nat.mul_succ, Nat.add_comm]

/-- Repeated actual normalized pure block input. -/
def repeatInput (k : ℕ) (ψ : UnitPureInput (a ^ k) (a ^ k)) :
    (m : ℕ) → UnitPureInput (a ^ blocks k m) (a ^ blocks k m)
  | 0 => maximallyEntangledInput (by decide : 0 < 1)
  | m + 1 => combineInput k (blocks k m) ψ (repeatInput k ψ m)

/-- Explicit product/reference regrouping for every repeated block. -/
def repeatOutput (a b k : ℕ) : (m : ℕ) →
    Fin ((a ^ k * b ^ k) ^ m) ≃ Fin (a ^ blocks k m * b ^ blocks k m)
  | 0 => Equiv.refl _
  | m + 1 => (statePowerJoin (a ^ k * b ^ k) m).symm.trans
      ((outputReindex (Equiv.refl _) (repeatOutput a b k m)).trans
        (combineOutput a b k (blocks k m)))

/-- Repeating the genuine pure block yields exactly the state tensor powers
under the same output permutation for every channel hypothesis. -/
theorem pureOutput_repeatInput (Φ : KrausChannel a b) (k : ℕ)
    (ψ : UnitPureInput (a ^ k) (a ^ k)) (m : ℕ) :
    pureOutput (Φ.tensorPower (blocks k m)) (repeatInput k ψ m) =
      (statePower (pureOutput (Φ.tensorPower k) ψ) m).reindex (repeatOutput a b k m) := by
  induction m with
  | zero => exact state_one_unique _ _
  | succ m ih =>
    change pureOutput (Φ.tensorPower (k + blocks k m)) (combineInput k (blocks k m) ψ _) = _
    rw [pureOutput_combineInput, ih, tensor_reindex_right, State.reindex_trans, statePower_succ,
      State.reindex_trans]
    congr 1

/-- A state test on repeated block outputs is an actual parallel channel test. -/
def repeatedTest (k m : ℕ) (T : Effect ((a ^ k * b ^ k) ^ m)) :
    Effect (a ^ blocks k m * b ^ blocks k m) := reindexEffect (repeatOutput a b k m) T

theorem repeatedTest_probability (Φ : KrausChannel a b) (k m : ℕ)
    (ψ : UnitPureInput (a ^ k) (a ^ k)) (T : Effect ((a ^ k * b ^ k) ^ m)) :
    (repeatedTest k m T).probability (pureOutput (Φ.tensorPower (blocks k m)) (repeatInput k ψ m)) =
      T.probability (statePower (pureOutput (Φ.tensorPower k) ψ) m) := by
  rw [pureOutput_repeatInput]
  exact reindexEffect_probability _ _ _

/-- Append an identity measurement to ignore an arbitrary finite output block. -/
def ignoreTail (T : Effect d) (e : ℕ) : Effect (d * e) := by
  let P := Matrix.reindex finProdFinEquiv finProdFinEquiv (T.matrix ⊗ₖ (1 : Operator e))
  have hP : P.PosSemidef :=
    (MatrixMap.posSemidef_kronecker T.positive Matrix.PosSemidef.one).submatrix _
  refine ⟨P, hP, ?_⟩
  letI : CStarAlgebra (Operator (d * e)) := CStarAlgebra.mk
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg P hP.nonneg).mp
  change ‖Matrix.reindex _ _ (T.matrix ⊗ₖ (1 : Operator e))‖ ≤ 1
  rw [norm_reindex]
  exact (TensorNorm.kronecker_one_opNorm_le T.matrix).trans T.norm_matrix_le_one

theorem ignoreTail_probability (T : Effect d) (ρ : State d) (σ : State d') :
    (ignoreTail T d').probability (ρ.tensor σ) = T.probability ρ := by
  change ((Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (T.matrix ⊗ₖ 1)) *
    (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv (ρ.matrix ⊗ₖ σ.matrix))).trace.re = _
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_apply, trace_reindex_equiv,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker, σ.trace_one, mul_one]
  rfl

/-- Exact remainder padding preserves both Born probabilities, not merely their bounds. -/
theorem padded_test (Φ Ψ : KrausChannel a b) (ha : 0 < a) (p q : ℕ)
    (ψ : UnitPureInput (a ^ p) (a ^ p)) (T : Effect (a ^ p * b ^ p)) :
    ∃ φ : UnitPureInput (a ^ (p + q)) (a ^ (p + q)), ∃ U : Effect (a ^ (p + q) * b ^ (p + q)),
      U.probability (pureOutput (Φ.tensorPower (p + q)) φ) = T.probability (pureOutput (Φ.tensorPower p) ψ) ∧
      U.probability (pureOutput (Ψ.tensorPower (p + q)) φ) = T.probability (pureOutput (Ψ.tensorPower p) ψ) := by
  let χ := unitProductInput (pow_pos ha q)
  let U := reindexEffect (combineOutput a b p q) (ignoreTail T (a ^ q * b ^ q))
  refine ⟨combineInput p q ψ χ, U, ?_, ?_⟩ <;>
    rw [pureOutput_combineInput, reindexEffect_probability, ignoreTail_probability]

/-- Repeated-block testing plus exact ignored-output padding is a literal
paper parallel pure test at every total blocklength. -/
theorem repeated_padded_test (Φ Ψ : KrausChannel a b) (ha : 0 < a) (k m ell : ℕ)
    (ψ : UnitPureInput (a ^ k) (a ^ k)) (T : Effect ((a ^ k * b ^ k) ^ m)) :
    ∃ φ : UnitPureInput (a ^ (k * m + ell)) (a ^ (k * m + ell)),
    ∃ U : Effect (a ^ (k * m + ell) * b ^ (k * m + ell)),
      U.probability (pureOutput (Φ.tensorPower (k * m + ell)) φ) =
        T.probability (statePower (pureOutput (Φ.tensorPower k) ψ) m) ∧
      U.probability (pureOutput (Ψ.tensorPower (k * m + ell)) φ) =
        T.probability (statePower (pureOutput (Ψ.tensorPower k) ψ) m) := by
  have h := padded_test Φ Ψ ha (blocks k m) ell (repeatInput k ψ m) (repeatedTest k m T)
  simp only [repeatedTest_probability] at h
  rw [← blocks_eq_mul k m]
  exact h

end QuantumChannelStein.ParallelBlockTests
