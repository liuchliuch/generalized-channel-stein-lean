import QuantumChannelStein.EnvironmentTensor
import QuantumChannelStein.Normalization

/-!
# Constructive fixed-block amplification

This is the actual finite-block construction used in Lemma 4.5: both its
retained auxiliary-map cost and its exponentially small dilation error are
proved. Selection of a sufficiently good block, rate absorption, and padding
to every external blocklength remain separate from this theorem.
-/
noncomputable section
namespace QuantumChannelStein.FixedBlockConstruction
open scoped Kronecker Matrix.Norms.L2Operator
open Matrix TensorPower TensorExpansion EnvironmentTensor

/-- An exact residual produces a single auxiliary map having both the retained
rate cost and the exponentially small operator error. No abstract tensor or
approximation interface is assumed. -/
theorem fixed_block_auxiliary {a b e f : Type*}
    [Fintype a] [Fintype b] [Fintype e] [Fintype f]
    [DecidableEq a] [DecidableEq b] [DecidableEq e] [DecidableEq f]
    (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ)
    (C D : Matrix e f ℂ) (l k : ℕ) (S L ε η : ℝ)
    (hVN : ‖VN‖ ≤ 1) (hexact : VN = applyEnvironment VM D)
    (happrox : ‖VN - applyEnvironment VM C‖ ≤ ε)
    (hε : 0 ≤ ε) (hη : 0 < η)
    (hsmall : ε ≤ 1 / (1 + (4 : ℝ) ^ (1 / η))) (hSL : S ≤ L)
    (hC : ‖C‖ ≤ (2 : ℝ) ^ ((l : ℝ) * S / 2))
    (hD : ‖D‖ ≤ (2 : ℝ) ^ ((l : ℝ) * L / 2)) :
    ∃ A : Matrix (Index e k) (Index f k) ℂ,
      ‖A‖ ≤ 3 ^ k * (2 : ℝ) ^ ((l : ℝ) * k * (S + η * (L - S)) / 2) ∧
      ‖blockDilation VN k - applyEnvironment (blockDilation VM k) A‖ ≤ (1 / 2 : ℝ) ^ k := by
  have hCL : ‖C‖ ≤ (2 : ℝ) ^ ((l : ℝ) * L / 2) :=
    hC.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSL (Nat.cast_nonneg l)) (by norm_num)))
  have hresidual : ‖D - C‖ ≤ 2 * (2 : ℝ) ^ ((l : ℝ) * L / 2) := by
    have h := (norm_sub_le D C).trans (add_le_add hD hCL)
    nlinarith
  have henvresidual : applyEnvironment VM (D - C) = VN - applyEnvironment VM C := by
    change environmentLinear VM (D - C) = VN - environmentLinear VM C
    rw [map_sub]
    exact congrArg (fun X => X - environmentLinear VM C) hexact.symm
  have henvnorm : ‖applyEnvironment VM C‖ ≤ 1 + ε :=
    Normalization.norm_approx_le hVN happrox
  have henvsmall : ‖applyEnvironment VM (D - C)‖ ≤ ε := by
    rw [henvresidual]
    exact happrox
  have hsum : applyEnvironment VM C + applyEnvironment VM (D - C) = VN := by
    rw [henvresidual]
    abel
  refine ⟨truncateAt C (D - C) k (η * k),
    operator_truncation_rate_cost C (D - C) l k S L η hSL hC hresidual, ?_⟩
  have herror := operator_truncation_half_pow (applyEnvironment VM C)
    (applyEnvironment VM (D - C)) hε hη henvnorm henvsmall hsmall k
  rw [← environment_truncate_error, hsum] at herror
  exact herror

end QuantumChannelStein.FixedBlockConstruction
