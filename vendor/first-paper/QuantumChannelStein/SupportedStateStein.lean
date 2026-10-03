import QuantumChannelStein.PerfectDiscrimination
import QuantumChannelStein.ParallelExponent

/-!
# Transparent ordinary supported-state direct Stein interface

This is an explicit premise to the channel assembly, not an axiom. Its
coordinate and probability conventions are the actual recursive matrix
tensor powers requested by the independent state-Stein source bridge.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ParallelSteinAssembly
open Matrix ChannelEntropy RelativeEntropy TensorPower ChannelPowerReindex PerfectDiscrimination Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

/-- Ordinary supported-state direct Stein statement, in literal matrix
coordinates and the paper's base-two rate convention. -/
def SupportedStateDirect : Prop :=
  ∀ (d : ℕ) (ρ σ : State d), supportIncluded ρ σ →
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ u : ℝ, 0 ≤ u → (u : EReal) < umegaki ρ σ →
      ∀ᶠ m : ℕ in atTop,
        ∃ T : Matrix (Index (Fin d) m) (Index (Fin d) m) ℂ,
          T.PosSemidef ∧ (1 - T).PosSemidef ∧
          (tensorPower ρ.matrix m * (1 - T)).trace.re ≤ ε ∧
          (tensorPower σ.matrix m * T).trace.re ≤ (2 : ℝ) ^ (-(m : ℝ) * u)

/-- The raw supported-state theorem gives actual effects on the existing
flattened genuine tensor state powers, with exact probability conversion. -/
theorem supportedStateDirect_effects (hstein : SupportedStateDirect)
    {d : ℕ} (ρ σ : State d) (hs : supportIncluded ρ σ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (u : ℝ) (hu : 0 ≤ u)
    (huD : (u : EReal) < umegaki ρ σ) :
    ∀ᶠ m : ℕ in atTop, ∃ T : Effect (d ^ m),
      1 - ε ≤ T.probability (statePower ρ m) ∧
      T.probability (statePower σ m) ≤ (2 : ℝ) ^ (-(m : ℝ) * u) := by
  filter_upwards [hstein d ρ σ hs ε hε hε1 u hu huD] with m hm
  obtain ⟨T, hT, hTc, herr, hq⟩ := hm
  let e := channelIndexEquiv d m
  have hc : (1 - Matrix.reindex e e T).PosSemidef := by
    have h := hTc.submatrix e.symm
    change (Matrix.reindexLinearEquiv ℂ ℂ e e (1 - T)).PosSemidef at h
    rw [map_sub, Matrix.reindexLinearEquiv_one] at h
    exact h
  let U : Effect (d ^ m) := ⟨Matrix.reindex e e T, hT.submatrix e.symm, hc⟩
  have hprob (τ : State d) : U.probability (statePower τ m) = (T * tensorPower τ.matrix m).trace.re := by
    change ((Matrix.reindexLinearEquiv ℂ ℂ e e T) *
      (Matrix.reindexLinearEquiv ℂ ℂ e e (tensorPower τ.matrix m))).trace.re = _
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_apply, trace_reindex_equiv]
  refine ⟨U, ?_, ?_⟩
  · rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, trace_tensorPower, ρ.trace_one,
      one_pow, Complex.sub_re, Complex.one_re, Matrix.trace_mul_comm] at herr
    rw [hprob]
    linarith
  · rw [hprob, Matrix.trace_mul_comm]
    exact hq

end QuantumChannelStein.ParallelSteinAssembly
