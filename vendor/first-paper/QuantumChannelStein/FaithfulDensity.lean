import QuantumChannelStein.GeometricMeanCongruence
import QuantumChannelStein.PositiveMarginalMinimax

/-! # Actual faithful density perturbations and inverse square roots -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.FaithfulDensity
open Matrix Pseudoinverse
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {n : ℕ}
local instance faithfulDensityCStar1 : CStarAlgebra (Operator n) := CStarAlgebra.mk

def maximallyMixed (n : ℕ) (hn : 0 < n) : State n where
  matrix := (n : ℝ)⁻¹ • (1 : Operator n)
  positive := Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg n))
  trace_one := by
    simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, Complex.real_smul]
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    push_cast
    exact inv_mul_cancel₀ hn0

theorem maximallyMixed_posDef (n : ℕ) (hn : 0 < n) : (maximallyMixed n hn).matrix.PosDef :=
  Matrix.PosDef.one.smul (inv_pos.mpr (Nat.cast_pos.mpr hn))

def mix (ρ σ : State n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : State n where
  matrix := (1 - t) • ρ.matrix + t • σ.matrix
  positive := (ρ.positive.smul (sub_nonneg.mpr ht1)).add (σ.positive.smul ht0)
  trace_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ρ.trace_one, σ.trace_one,
      ← add_smul, sub_add_cancel, one_smul]

theorem mix_posDef (ρ σ : State n) (hσ : σ.matrix.PosDef)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (mix ρ σ t ht0.le ht1).matrix.PosDef :=
  Matrix.PosDef.posSemidef_add (ρ.positive.smul (sub_nonneg.mpr ht1)) (hσ.smul ht0)

theorem supportProjection_eq_one (B : Operator n) (hB : B.PosDef) :
    supportProjection B hB.posSemidef = 1 := by
  unfold supportProjection
  rw [← hB.posSemidef.isHermitian.cfc_eq]
  calc
    cfc (fun x : ℝ => if x = 0 then 0 else 1) B = cfc (fun _ : ℝ => 1) B := by
      apply cfc_congr
      intro x hx
      rw [hB.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      simp [(hB.eigenvalues_pos i).ne']
    _ = 1 := cfc_const_one ℝ B


theorem root_inverseSqrt (B : Operator n) (hB : B.PosDef) :
    root B hB.posSemidef * inverseSqrt B hB.posSemidef = 1 := by
  rw [root_mul_inverseSqrt, supportProjection_eq_one B hB]

theorem inverseSqrt_root (B : Operator n) (hB : B.PosDef) :
    inverseSqrt B hB.posSemidef * root B hB.posSemidef = 1 := by
  rw [inverseSqrt_mul_root, supportProjection_eq_one B hB]

/-- Positive marginal expectations are controlled by the faithful perturbation. -/
theorem expectation_mix_lower (ρ σ : State n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Operator n) (hH : H.PosSemidef) :
    (1 - t) * (H * ρ.matrix).trace.re ≤ (H * (mix ρ σ t ht0 ht1).matrix).trace.re := by
  have hnonneg := (Complex.nonneg_iff.mp (TestingSDP.trace_pairing_nonnegative hH σ.positive)).1
  change _ ≤ (H * ((1 - t) • ρ.matrix + t • σ.matrix)).trace.re
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul]
  exact le_add_of_nonneg_right (mul_nonneg ht0 hnonneg)

end QuantumChannelStein.FaithfulDensity
