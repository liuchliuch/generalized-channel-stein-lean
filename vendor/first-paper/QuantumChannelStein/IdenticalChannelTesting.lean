import QuantumChannelStein.AdaptiveTesting

/-! # Exact fixed-error testing for identical channels

This checks the elementary example immediately after Theorem 2.1: p=q
and the parallel optimum equals 1-epsilon. The adaptive optimum agrees too.
-/
noncomputable section
namespace QuantumChannelStein.IdenticalChannelTesting
open Matrix ChannelEntropy OperationalTesting AdaptiveProtocol
open scoped ComplexOrder

/-- A state-independent randomized binary effect. -/
def coinEffect (d : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : Effect d where
  matrix := p • (1 : Operator d)
  positive := Matrix.PosSemidef.one.smul hp
  complement_positive := by
    have h := (Matrix.PosSemidef.one : (1 : Operator d).PosSemidef).smul
      (sub_nonneg.mpr hp1)
    simpa only [sub_smul, one_smul] using h

@[simp] theorem coinEffect_probability (d : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : State d) : (coinEffect d p hp hp1).probability ρ = p := by
  simp [coinEffect, Effect.probability, Matrix.smul_mul, Matrix.trace_smul, ρ.trace_one]

theorem parallelPureBeta_self {a b : ℕ} (Φ : KrausChannel a b) (ha : 0 < a)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    parallelPureBeta Φ Φ n ε = ENNReal.ofReal (1-ε) := by
  apply le_antisymm
  · let ψ := maximallyEntangledInput (pow_pos ha n)
    let T := coinEffect (a^n*b^n) (1-ε) (sub_nonneg.mpr hε1) (by linarith)
    refine iInf_le_of_le ⟨(ψ,T), ?_⟩ ?_
    · simp [T]
    · simp [T]
  · apply le_iInf
    intro t
    exact ENNReal.ofReal_le_ofReal t.property

theorem parallelBeta_self {a b : ℕ} (Φ : KrausChannel a b) (ha : 0 < a)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    parallelBeta Φ Φ n ε = ENNReal.ofReal (1-ε) := by
  apply le_antisymm
  · exact (parallelBeta_le_parallelPureBeta Φ Φ n ε).trans_eq
      (parallelPureBeta_self Φ ha n ε hε hε1)
  · apply le_iInf
    intro t
    exact ENNReal.ofReal_le_ofReal t.property

theorem adaptiveBeta_self {a b : ℕ} (Φ : KrausChannel a b) (ha : 0 < a)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    adaptiveBeta Φ Φ n ε = ENNReal.ofReal (1-ε) := by
  apply le_antisymm
  · exact (adaptiveBeta_le_parallelPureBeta Φ Φ n ε).trans_eq
      (parallelPureBeta_self Φ ha n ε hε hε1)
  · apply le_iInf
    intro P
    exact ENNReal.ofReal_le_ofReal P.property

end QuantumChannelStein.IdenticalChannelTesting
