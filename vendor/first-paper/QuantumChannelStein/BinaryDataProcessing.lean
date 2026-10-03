import QuantumChannelStein.RelativeEntropyDPIBridge
import QuantumChannelStein.BinaryStates
import QuantumChannelStein.BinaryEntropyBounds

/-! # Actual binary measurement data processing and the state testing bound

The channel below is the normalized finite Kraus measurement of the effect.
The binary trace formula is compared with support-aware Umegaki at all
probability endpoints. In particular no positivity assumption on the
alternative acceptance is used in the testing bound.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.BinaryMeasurement
open Matrix RelativeEntropy BinaryEntropyBounds
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

private theorem state_eq_of_matrix_eq {ρ σ : State n} (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

theorem channel_onState (T : Effect n) (ρ : State n) :
    (channel T).onState ρ =
      binaryState (T.probability ρ) (T.probability_nonneg ρ) (T.probability_le_one ρ) :=
  state_eq_of_matrix_eq (channel_onState_matrix T ρ)

theorem binary_traceFormula (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    traceFormula (binaryState p hp0 hp1) (binaryState q hq0 hq1) =
      binaryRelativeEntropy p q := by
  unfold traceFormula
  rw [binary_spectralLog2, binary_spectralLog2]
  simp [binaryState, binaryRelativeEntropy, Matrix.diagonal_sub,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_two, Complex.mul_re]

/-- The totalized real binary formula is a lower bound on the genuine
extended divergence even when the alternative has a zero probability. -/
theorem binaryRelativeEntropy_le_umegaki (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (binaryRelativeEntropy p q : EReal) ≤
      umegaki (binaryState p hp0 hp1) (binaryState q hq0 hq1) := by
  by_cases hs : supportIncluded (binaryState p hp0 hp1) (binaryState q hq0 hq1)
  · rw [umegaki_of_supportIncluded _ _ hs, binary_traceFormula]
  · rw [umegaki_of_not_supportIncluded _ _ hs]
    exact le_top

/-- Binary measurement DPI for an actual effect and arbitrary density matrices,
with no interior-probability or full-rank restriction. -/
theorem binary_measurement_data_processing (T : Effect n) (ρ σ : State n) :
    (binaryRelativeEntropy (T.probability ρ) (T.probability σ) : EReal) ≤ umegaki ρ σ := by
  have h := RelativeEntropy.umegaki_data_processing (channel T) ρ σ
  rw [channel_onState, channel_onState] at h
  exact (binaryRelativeEntropy_le_umegaki _ _
    (T.probability_nonneg ρ) (T.probability_le_one ρ)
    (T.probability_nonneg σ) (T.probability_le_one σ)).trans h

/-- PSD domination implies domination of every actual Born probability. -/
theorem probability_le_of_domination (T : Effect n) (ρ σ : State n) (c : ℝ)
    (h : (c • σ.matrix - ρ.matrix).PosSemidef) :
    T.probability ρ ≤ c * T.probability σ := by
  have ht := (Complex.nonneg_iff.mp (trace_mul_nonnegative T.positive h)).1
  simpa only [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, sub_nonneg] using ht

/-- State-level testing estimate underlying Lemma 4.3. The finite entropy upper
bound entails the required support condition, including zero acceptance. -/
theorem hockeyStick_le_min_of_umegaki_le (T : Effect n) (ρ σ : State n)
    (D x : ℝ) (hx : 0 < x) (hD : umegaki ρ σ ≤ (D : EReal)) :
    T.probability ρ - (2 : ℝ) ^ x * T.probability σ ≤ min 1 ((D + 1) / x) := by
  have hreal : binaryRelativeEntropy (T.probability ρ) (T.probability σ) ≤ D :=
    EReal.coe_le_coe_iff.mp ((binary_measurement_data_processing T ρ σ).trans hD)
  obtain ⟨c, hc, hdom⟩ := (umegaki_lt_top_iff_exists_domination ρ σ).mp
    (lt_of_le_of_lt hD (EReal.coe_lt_top D))
  exact BinaryEntropyBounds.hockeyStick_le_min_of_domination
    (T.probability_nonneg ρ) (T.probability_le_one ρ)
    (T.probability_nonneg σ) (T.probability_le_one σ) hx hreal
    (probability_le_of_domination T ρ σ c hdom)

end QuantumChannelStein.BinaryMeasurement
