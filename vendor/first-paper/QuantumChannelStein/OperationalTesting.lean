import QuantumChannelStein.PerfectDiscrimination

/-!
# Operational parallel binary testing and support-failure discrimination

The unrestricted operational test class permits every finite reference,
every mixed joint input, and every binary effect on the actual amplified
output. Its infimum is taken in `ENNReal`: nonnegative Born probabilities
embed faithfully and the empty feasible set has value infinity.

`parallelPureBeta` is the literal pure-input, fixed-reference normal form
of equation (2.4) of arXiv:2609.27196v1. Both optimizations are proved to
vanish under Proposition 3.6's support-failure condition. This file does
not assume their general equivalence by purification/Schmidt reduction.
-/
noncomputable section
namespace QuantumChannelStein.OperationalTesting
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open Matrix ChannelEntropy PerfectDiscrimination

variable {n m r : ℕ}

/-- The actual mixed reference-assisted output state, in flattened coordinates. -/
def outputState (Φ : KrausChannel n m) (r : ℕ) (ρ : State (r * n)) : State (r * m) where
  matrix := Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Φ.amplify r (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm ρ.matrix))
  positive := (Φ.amplify_positive r (ρ.positive.submatrix finProdFinEquiv)).submatrix
    finProdFinEquiv.symm
  trace_one := by
    rw [trace_reindex_equiv, Φ.trace_amplify, trace_reindex_equiv, ρ.trace_one]

/-- An arbitrary finite-reference, possibly mixed-input channel test. -/
structure ChannelTest (n m : ℕ) where
  reference : ℕ
  input : State (reference * n)
  effect : Effect (reference * m)

/-- Actual null or alternative acceptance of the test, depending on the channel. -/
def ChannelTest.acceptance (t : ChannelTest n m) (Φ : KrausChannel n m) : ℝ :=
  t.effect.probability (outputState Φ t.reference t.input)

theorem ChannelTest.acceptance_nonneg (t : ChannelTest n m) (Φ : KrausChannel n m) :
    0 ≤ t.acceptance Φ := t.effect.probability_nonneg _

theorem ChannelTest.acceptance_le_one (t : ChannelTest n m) (Φ : KrausChannel n m) :
    t.acceptance Φ ≤ 1 := t.effect.probability_le_one _

/-- Parallel type-II optimization over the full finite-reference mixed-input
operational class, under the type-I constraint. -/
def parallelBeta (Φ Ψ : KrausChannel n m) (k : ℕ) (ε : ℝ) : ENNReal :=
  ⨅ t : {t : ChannelTest (n ^ k) (m ^ k) //
    1 - ε ≤ t.acceptance (KrausChannel.tensorPower Φ k)},
      ENNReal.ofReal (t.val.acceptance (KrausChannel.tensorPower Ψ k))

/-- Literal equation (2.4): pure input with reference dimension equal to the
input dimension, followed by an arbitrary binary output effect. -/
def parallelPureBeta (Φ Ψ : KrausChannel n m) (k : ℕ) (ε : ℝ) : ENNReal :=
  ⨅ t : {t : UnitPureInput (n ^ k) (n ^ k) × Effect (n ^ k * m ^ k) //
    1 - ε ≤ t.2.probability (pureOutput (KrausChannel.tensorPower Φ k) t.1)},
      ENNReal.ofReal (t.val.2.probability (pureOutput (KrausChannel.tensorPower Ψ k) t.val.1))

/-- A pure input is also a genuine mixed-input density matrix. -/
def pureInputState (ψ : UnitPureInput r n) : State (r * n) where
  matrix := Matrix.reindex finProdFinEquiv finProdFinEquiv (pureMatrix ψ.val)
  positive := (pureMatrix_positive ψ.val).submatrix _
  trace_one := by
    rw [trace_reindex_equiv]
    exact trace_pureMatrix_of_norm_one ψ.val ψ.property

/-- The mixed-input implementation agrees with the original pure-output semantics. -/
theorem outputState_pureInputState_matrix (Φ : KrausChannel n m)
    (ψ : UnitPureInput r n) :
    (outputState Φ r (pureInputState ψ)).matrix = (pureOutput Φ ψ).matrix := by
  have h : Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (pureInputState ψ).matrix = pureMatrix ψ.val := by
    ext i j
    simp [pureInputState, Matrix.reindex_apply]
  change Matrix.reindex _ _ (Φ.amplify r _) = _
  rw [h]
  rfl

/-- Every fixed-reference pure test belongs to the unrestricted operational class. -/
def ofPureTest (ψ : UnitPureInput r n) (T : Effect (r * m)) : ChannelTest n m :=
  ⟨r, pureInputState ψ, T⟩

@[simp] theorem ofPureTest_acceptance (Φ : KrausChannel n m)
    (ψ : UnitPureInput r n) (T : Effect (r * m)) :
    (ofPureTest ψ T).acceptance Φ = T.probability (pureOutput Φ ψ) := by
  change (T.matrix * (outputState Φ r (pureInputState ψ)).matrix).trace.re = _
  rw [outputState_pureInputState_matrix]
  rfl

/-- A feasible actual zero-error test forces the unrestricted optimum to zero. -/
theorem parallelBeta_eq_zero_of_test (Φ Ψ : KrausChannel n m) (k : ℕ) (ε : ℝ)
    (t : ChannelTest (n ^ k) (m ^ k))
    (hp : 1 - ε ≤ t.acceptance (KrausChannel.tensorPower Φ k))
    (hq : t.acceptance (KrausChannel.tensorPower Ψ k) = 0) :
    parallelBeta Φ Ψ k ε = 0 := by
  apply le_antisymm _ bot_le
  exact (iInf_le (fun t : {t : ChannelTest (n ^ k) (m ^ k) //
    1 - ε ≤ t.acceptance (KrausChannel.tensorPower Φ k)} =>
      ENNReal.ofReal (t.val.acceptance (KrausChannel.tensorPower Ψ k))) ⟨t, hp⟩).trans
        (by simp [hq])

/-- A feasible pure zero-error test also forces the literal paper optimum to zero. -/
theorem parallelPureBeta_eq_zero_of_test (Φ Ψ : KrausChannel n m) (k : ℕ) (ε : ℝ)
    (ψ : UnitPureInput (n ^ k) (n ^ k)) (T : Effect (n ^ k * m ^ k))
    (hp : 1 - ε ≤ T.probability (pureOutput (KrausChannel.tensorPower Φ k) ψ))
    (hq : T.probability (pureOutput (KrausChannel.tensorPower Ψ k) ψ) = 0) :
    parallelPureBeta Φ Ψ k ε = 0 := by
  apply le_antisymm _ bot_le
  exact (iInf_le (fun t : {t : UnitPureInput (n ^ k) (n ^ k) × Effect (n ^ k * m ^ k) //
    1 - ε ≤ t.2.probability (pureOutput (KrausChannel.tensorPower Φ k) t.1)} =>
      ENNReal.ofReal (t.val.2.probability (pureOutput (KrausChannel.tensorPower Ψ k) t.val.1)))
        ⟨(ψ, T), hp⟩).trans (by simp [hq])

/-- Proposition 3.6, optimal-error conclusion for the unrestricted operational
parallel test class, with exactly the paper's fixed-error range. -/
theorem support_failure_zero_type_two (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (h : ¬ LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin)
    (ε : ℝ) (hε : 0 < ε) (_hεone : ε < 1) :
    ∀ᶠ k : ℕ in Filter.atTop, parallelBeta Φ Ψ k ε = 0 := by
  filter_upwards [eventually_exists_parallel_test Φ Ψ hn h ε hε] with k hk
  obtain ⟨T, hp, hq⟩ := hk
  apply parallelBeta_eq_zero_of_test Φ Ψ k ε
    (ofPureTest (maximallyEntangledInput (pow_pos hn k)) T)
  · simpa only [ofPureTest_acceptance] using hp
  · simpa only [ofPureTest_acceptance] using hq

/-- Proposition 3.6, optimal-error conclusion for the literal pure-input
fixed-reference definition in equation (2.4). -/
theorem support_failure_zero_type_two_pure (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (h : ¬ LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin)
    (ε : ℝ) (hε : 0 < ε) (_hεone : ε < 1) :
    ∀ᶠ k : ℕ in Filter.atTop, parallelPureBeta Φ Ψ k ε = 0 := by
  filter_upwards [eventually_exists_parallel_test Φ Ψ hn h ε hε] with k hk
  obtain ⟨T, hp, hq⟩ := hk
  exact parallelPureBeta_eq_zero_of_test Φ Ψ k ε
    (maximallyEntangledInput (pow_pos hn k)) T hp hq

/-- The full operational test class contains every test in the pure normal form. -/
theorem parallelBeta_le_parallelPureBeta (Φ Ψ : KrausChannel n m) (k : ℕ) (ε : ℝ) :
    parallelBeta Φ Ψ k ε ≤ parallelPureBeta Φ Ψ k ε := by
  apply le_iInf
  intro t
  refine iInf_le_of_le ⟨ofPureTest t.val.1 t.val.2, ?_⟩ ?_
  · simpa only [ofPureTest_acceptance] using t.property
  · simp only [ofPureTest_acceptance, le_refl]

/-- A deterministic accept effect. -/
def acceptAll (d : ℕ) : Effect d where
  matrix := 1
  positive := Matrix.PosSemidef.one
  complement_positive := by
    simpa only [sub_self] using (Matrix.PosSemidef.zero : (0 : Operator d).PosSemidef)

@[simp] theorem acceptAll_probability {d : ℕ} (ρ : State d) :
    (acceptAll d).probability ρ = 1 := by
  simp [acceptAll, Effect.probability, ρ.trace_one]

/-- In the physical tolerance range the literal paper optimum is an ordinary
probability, so the extended codomain introduces no spurious infinities. -/
theorem parallelPureBeta_le_one (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) : parallelPureBeta Φ Ψ k ε ≤ 1 := by
  refine iInf_le_of_le ⟨(maximallyEntangledInput (pow_pos hn k), acceptAll _), ?_⟩ ?_
  · simp only [acceptAll_probability]
    linarith only [hε]
  · simp only [acceptAll_probability, ENNReal.ofReal_one, le_refl]

/-- The unrestricted parallel optimum also lies between zero and one. -/
theorem parallelBeta_le_one (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) : parallelBeta Φ Ψ k ε ≤ 1 :=
  (parallelBeta_le_parallelPureBeta Φ Ψ k ε).trans (parallelPureBeta_le_one Φ Ψ hn k ε hε)

/-- Proposition 3.6 of arXiv:2609.27196v1, including the concrete test family
and the eventual zero optimum with the literal equation (2.4) definition. -/
theorem proposition_3_6 (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (h : ¬ LinearMap.ker Ψ.choi.mulVecLin ≤ LinearMap.ker Φ.choi.mulVecLin) :
    (∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ ∀ k : ℕ, 1 ≤ k →
      ∃ ψ : UnitPureInput (n ^ k) (n ^ k), ∃ T : Effect (n ^ k * m ^ k),
        T.probability (pureOutput (KrausChannel.tensorPower Φ k) ψ) = 1 - (1 - lam) ^ k ∧
        T.probability (pureOutput (KrausChannel.tensorPower Ψ k) ψ) = 0) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ᶠ k : ℕ in Filter.atTop, parallelPureBeta Φ Ψ k ε = 0) := by
  constructor
  · obtain ⟨lam, hpos, hone, T, hT⟩ := exists_parallel_zero_error_tests Φ Ψ hn h
    refine ⟨lam, hpos, hone, ?_⟩
    intro k _
    exact ⟨maximallyEntangledInput (pow_pos hn k), T k, hT k⟩
  · exact fun ε hε hεone => support_failure_zero_type_two_pure Φ Ψ hn h ε hε hεone

end QuantumChannelStein.OperationalTesting
