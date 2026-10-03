import QuantumChannelStein.UniformApproximation

/-! # Actual two-rate tensor block construction for Lemma 4.4 -/
noncomputable section
namespace QuantumChannelStein.TwoRateBlock
open scoped Kronecker Matrix.Norms.L2Operator
open Matrix TensorPower TensorExpansion EnvironmentTensor UniformApproximation

variable {a b e f : Type*}
  [Fintype a] [Fintype b] [Fintype e] [Fintype f]
  [DecidableEq a] [DecidableEq b] [DecidableEq e] [DecidableEq f]

omit [DecidableEq b] [DecidableEq e] in
/-- Regrouping preserves differences of dilation tensors. -/
theorem norm_blockDilation_sub (U W : Matrix (b × e) a ℂ) (k : ℕ) :
    ‖blockDilation U k - blockDilation W k‖ = ‖tensorPower U k - tensorPower W k‖ := by
  have heq : blockDilation U k - blockDilation W k =
      Matrix.reindex (indexProdEquiv b e k) (Equiv.refl (Index a k))
        (tensorPower U k - tensorPower W k) := rfl
  rw [heq, TensorPower.norm_reindex]

/-- Combining a weak low-rate auxiliary and an accurate higher-rate auxiliary
produces the two simultaneous bounds in the block step of Lemma 4.4. The
weighted Chernoff tail is explicit, with no entropy or truncation oracle. -/
theorem two_rate_block_auxiliary
    (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ)
    (C D : Matrix e f ℂ) (l k : ℕ) (r S δ ε β z : ℝ)
    (hU : ‖U‖ ≤ 1) (hweak : ‖U - applyEnvironment V C‖ ≤ δ)
    (hstrong : ‖U - applyEnvironment V D‖ ≤ ε)
    (_hε : 0 ≤ ε) (_hδ : 0 ≤ δ) (hsmall : ε ≤ (1 - δ) / 2)
    (hrS : r ≤ S) (hz : 1 ≤ z)
    (hC : ‖C‖ ≤ (2 : ℝ) ^ ((l : ℝ) * r / 2))
    (hD : ‖D‖ ≤ (2 : ℝ) ^ ((l : ℝ) * S / 2)) :
    ∃ A : Matrix (Index e k) (Index f k) ℂ,
      ‖A‖ ≤ 3 ^ k * (2 : ℝ) ^ ((l : ℝ) * k * (r + β * (S - r)) / 2) ∧
      ‖blockDilation U k - applyEnvironment (blockDilation V k) A‖ ≤
        z ^ (-(β * k)) * (1 + δ + z * ((1 + δ) / 2)) ^ k +
          (k : ℝ) * ε * (1 + ε) ^ (k - 1) := by
  let X := applyEnvironment V C
  let Y := applyEnvironment V D
  let H := applyEnvironment V (D - C)
  have hH : H = Y - X := by
    change environmentLinear V (D - C) = environmentLinear V D - environmentLinear V C
    exact map_sub _ _ _
  have hsum : X + H = Y := by rw [hH]; abel
  have hXnorm : ‖X‖ ≤ 1 + δ := Normalization.norm_approx_le hU hweak
  have hYerror : ‖Y - U‖ ≤ ε := by rw [norm_sub_rev]; exact hstrong
  have hHnorm : ‖H‖ ≤ (1 + δ) / 2 := by
    rw [hH]
    have hdecomp : Y - X = (Y - U) + (U - X) := by abel
    rw [hdecomp]
    have hbound := (norm_add_le (Y - U) (U - X)).trans (add_le_add hYerror hweak)
    linarith
  have hCS : ‖C‖ ≤ (2 : ℝ) ^ ((l : ℝ) * S / 2) :=
    hC.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrS (Nat.cast_nonneg l)) (by norm_num)))
  have hresidual : ‖D - C‖ ≤ 2 * (2 : ℝ) ^ ((l : ℝ) * S / 2) := by
    have h := (norm_sub_le D C).trans (add_le_add hD hCS)
    nlinarith
  refine ⟨truncateAt C (D - C) k (β * k),
    operator_truncation_rate_cost C (D - C) l k r S β hrS hC hresidual, ?_⟩
  have htail := operator_truncation_bound X H hXnorm hHnorm hz k (β * k)
  rw [← environment_truncate_error V C (D - C), hsum] at htail
  have hrepeat : ‖blockDilation U k - blockDilation Y k‖ ≤
      (k : ℝ) * ε * (1 + ε) ^ (k - 1) := by
    rw [norm_blockDilation_sub, norm_sub_rev]
    exact norm_tensorPower_sub_le Y U hYerror hU k
  have htri := norm_sub_le_norm_sub_add_norm_sub (blockDilation U k) (blockDilation Y k)
    (applyEnvironment (blockDilation V k) (truncateAt C (D - C) k (β * k)))
  exact htri.trans (by linarith)

end QuantumChannelStein.TwoRateBlock
