import QuantumChannelStein.TwoRateBlock
import QuantumChannelStein.TensorBlockReindex

/-! # Physical construction for the variable-block two-rate step -/
noncomputable section
namespace QuantumChannelStein.TwoRateConstruction
open scoped Kronecker Matrix.Norms.L2Operator Topology
open Matrix TensorPower EnvironmentTensor UniformApproximation TensorBlockReindex Filter

variable {a b e f : Type*}
  [Fintype a] [Fintype b] [Fintype e] [Fintype f]
  [DecidableEq a] [DecidableEq b] [DecidableEq e] [DecidableEq f]

/-- The exact stretched-exponential rate property used in Lemma 4.4. -/
def StretchedAtRate (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ) (S : ℝ) : Prop :=
  ∃ K γ α : ℝ, 0 < K ∧ 0 < γ ∧ 0 < α ∧ α ≤ 1 ∧
    ∀ᶠ n : ℕ in atTop, ApproxAt U V n S (K * Real.exp (-γ * (n : ℝ) ^ α))

/-- The global exact comparison initializes the stretched-exponential rate iteration. -/
theorem stretched_of_exact (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ)
    (D : Matrix e f ℂ) (L : ℝ) (hexact : U = applyEnvironment V D)
    (hD : ‖D‖ ≤ (2 : ℝ) ^ (L / 2)) : StretchedAtRate U V L := by
  refine ⟨1,1,1,by norm_num,by norm_num,by norm_num,le_rfl,Filter.Eventually.of_forall ?_⟩
  intro n
  exact approxAt_mono U V n le_rfl (by positivity) (exact_approxAt U V D L hexact hD n)

/-- Two-rate truncation, canonical block flattening, and exact residual padding,
assembled at an arbitrary concrete decomposition `l*k+q`. The next analytic
step chooses these blocklengths; no asymptotic cost/error conclusion is assumed here. -/
theorem two_rate_padded_block
    (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ) (Dstar : Matrix e f ℂ)
    (L r S δ ε β z : ℝ) (l k q : ℕ)
    (hU : ‖U‖ ≤ 1) (hexact : U = applyEnvironment V Dstar)
    (hDstar : ‖Dstar‖ ≤ (2 : ℝ) ^ (L / 2))
    (hweak : ApproxAt U V l r δ) (hstrong : ApproxAt U V l S ε)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hsmall : ε ≤ (1 - δ) / 2)
    (hrS : r ≤ S) (hz : 1 ≤ z) :
    ∃ A : Matrix (Index e (l * k + q)) (Index f (l * k + q)) ℂ,
      ‖A‖ ≤ (3 ^ k * (2 : ℝ) ^ ((l : ℝ) * k * (r + β * (S - r)) / 2)) *
          (2 : ℝ) ^ ((q : ℝ) * L / 2) ∧
      auxiliaryError U V (l * k + q) A ≤
        z ^ (-(β * k)) * (1 + δ + z * ((1 + δ) / 2)) ^ k +
          (k : ℝ) * ε * (1 + ε) ^ (k - 1) := by
  obtain ⟨C,hC,hCerror⟩ := hweak
  obtain ⟨D,hD,hDerror⟩ := hstrong
  obtain ⟨A,hAnorm,hAerror⟩ := TwoRateBlock.two_rate_block_auxiliary
    (blockDilation U l) (blockDilation V l) C D l k r S δ ε β z
    (norm_blockDilation_le_one U hU l) hCerror hDerror hε hδ hsmall hrS hz hC hD
  let B := flattenAuxiliary l k A
  have hBnorm : ‖B‖ ≤ 3 ^ k * (2 : ℝ) ^ ((l : ℝ) * k * (r + β * (S - r)) / 2) := by
    simpa only [B, norm_flattenAuxiliary] using hAnorm
  have hBerror : auxiliaryError U V (l * k) B ≤
      z ^ (-(β * k)) * (1 + δ + z * ((1 + δ) / 2)) ^ k +
        (k : ℝ) * ε * (1 + ε) ^ (k - 1) := by
    change auxiliaryError U V (l * k) (flattenAuxiliary l k A) ≤ _
    rw [auxiliaryError_flattenAuxiliary]
    exact hAerror
  obtain ⟨Dq,hDq,hDqerror⟩ := exact_approxAt U V Dstar L hexact hDstar q
  have hDqExact : blockDilation U q = applyEnvironment (blockDilation V q) Dq := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm hDqerror (norm_nonneg _)
  refine ⟨padAuxiliary (l * k) q B Dq, ?_, ?_⟩
  · exact (norm_padAuxiliary_le _ _ B Dq).trans
      (mul_le_mul hBnorm hDq (norm_nonneg _) (by positivity))
  · exact (auxiliaryError_padAuxiliary_le U V _ _ B Dq hDqExact
      (norm_blockDilation_le_one U hU q)).trans hBerror

end QuantumChannelStein.TwoRateConstruction
