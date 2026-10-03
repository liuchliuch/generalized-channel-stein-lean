import QuantumChannelStein.SpectralPinching
import QuantumChannelStein.RelativeEntropyBound
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! # Exact entropy loss under the genuine spectral pinching channel -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.PinchingEntropy
open QuantumChannelStein QuantumChannelStein.RelativeEntropy Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Distinct spectral blocks are orthogonal as actual matrices. -/
theorem projection_mul (σ : State n) (v w : SpectralPinching.Block σ) :
    SpectralPinching.projection σ v * SpectralPinching.projection σ w =
      if v = w then SpectralPinching.projection σ v else 0 := by
  classical
  by_cases hvw : v = w
  · subst w; simp [SpectralPinching.projection_square]
  · rw [if_neg hvw]
    unfold SpectralPinching.projection
    rw [← map_mul]
    have hzero : SpectralPinching.blockDiagonal σ v * SpectralPinching.blockDiagonal σ w = 0 := by
      ext i
      simp only [Pi.mul_apply, Pi.zero_apply, SpectralPinching.blockDiagonal]
      split_ifs with hv hw hw
      · exact False.elim (hvw (Subtype.ext (hv.symm.trans hw)))
      all_goals simp
    rw [hzero, map_zero]

/-- A pinched operator commutes with each of the actual spectral blocks. -/
theorem pinched_commutes_projection (σ : State n) (A : Operator n)
    (v : SpectralPinching.Block σ) :
    Commute ((SpectralPinching.channel σ).apply A) (SpectralPinching.projection σ v) := by
  classical
  unfold Commute SemiconjBy
  rw [SpectralPinching.channel_apply, Finset.sum_mul, Finset.mul_sum]
  simp only [Matrix.mul_assoc, projection_mul]
  simp only [← Matrix.mul_assoc, projection_mul]
  simp [ite_mul, mul_ite]

/-- Pinching is self-adjoint for the trace pairing, when the second operator is block diagonal. -/
theorem trace_pinched_mul (σ : State n) (A B : Operator n)
    (hB : ∀ v : SpectralPinching.Block σ, Commute B (SpectralPinching.projection σ v)) :
    (((SpectralPinching.channel σ).apply A) * B).trace = (A * B).trace := by
  classical
  rw [SpectralPinching.channel_apply, Finset.sum_mul, Matrix.trace_sum]
  calc
    ∑ v : SpectralPinching.Block σ, (SpectralPinching.projection σ v * A * SpectralPinching.projection σ v * B).trace =
        ∑ v : SpectralPinching.Block σ, (A * B * SpectralPinching.projection σ v).trace := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
      rw [← Matrix.mul_assoc, Matrix.mul_assoc A (SpectralPinching.projection σ v) B,
        ← (hB v).eq, ← Matrix.mul_assoc A B, Matrix.mul_assoc,
        SpectralPinching.projection_square]
    _ = (A * B).trace := by
      rw [← Matrix.trace_sum, ← Finset.mul_sum, SpectralPinching.sum_projection, Matrix.mul_one]

/-- The exact trace-formula Pythagorean identity; no faithfulness is needed. -/
theorem traceFormula_pinching_identity (ρ σ : State n) :
    traceFormula ρ σ = traceFormula ρ ((SpectralPinching.channel σ).onState ρ) +
      traceFormula ((SpectralPinching.channel σ).onState ρ) σ := by
  let ρ' := (SpectralPinching.channel σ).onState ρ
  have hlogρ : (ρ'.matrix * spectralLog2 ρ').trace = (ρ.matrix * spectralLog2 ρ').trace := by
    apply trace_pinched_mul
    intro v
    rw [spectralLog2_eq_cfc]
    exact (pinched_commutes_projection σ ρ.matrix v).cfc_real _
  have hlogσ : (ρ'.matrix * spectralLog2 σ).trace = (ρ.matrix * spectralLog2 σ).trace := by
    apply trace_pinched_mul
    intro v
    rw [spectralLog2_eq_cfc]
    apply Commute.cfc_real
    exact (SpectralPinching.sigma_mul_projection σ v).trans
      (SpectralPinching.projection_mul_sigma σ v).symm
  change traceFormula ρ σ = traceFormula ρ ρ' + traceFormula ρ' σ
  simp only [traceFormula, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [hlogρ, hlogσ]
  ring

/-- Pinching loses at most the logarithm of its actual number of spectral blocks. -/
theorem traceFormula_pinching_loss (ρ σ : State n) :
    traceFormula ρ σ - Real.logb 2 (Fintype.card (SpectralPinching.Block σ)) ≤
      traceFormula ((SpectralPinching.channel σ).onState ρ) σ := by
  have hn : 0 < n := MatrixOperatorBridge.state_dimension_pos ρ
  have hcard : 1 ≤ (Fintype.card (SpectralPinching.Block σ) : ℝ) := by
    have hv : Nonempty (SpectralPinching.Block σ) :=
      ⟨SpectralPinching.eigenvalueIndex σ ⟨0, hn⟩⟩
    have hc := Fintype.card_pos_iff.mpr hv
    exact_mod_cast hc
  have hbound := traceFormula_le_log2_of_domination ρ
    ((SpectralPinching.channel σ).onState ρ)
    (Fintype.card (SpectralPinching.Block σ)) hcard
    (SpectralPinching.domination σ ρ.matrix ρ.positive)
  have hid := traceFormula_pinching_identity ρ σ
  linarith

end GeneralizedChannelStein.PinchingEntropy
