import QuantumChannelStein.TensorBlockReindex
import QuantumChannelStein.FixedBlockRates

/-!
# Fixed-block exponential amplification

Lemma 4.5 is proved for actual matrix dilations and their prescribed tensor
power environments. Tensor words, norm bounds, block flattening, and exact
remainder padding are proved in the imported modules rather than assumed.
-/
noncomputable section
namespace QuantumChannelStein.ExponentialAmplification
open scoped Kronecker Matrix.Norms.L2Operator Topology
open Matrix TensorPower EnvironmentTensor UniformApproximation TensorBlockReindex Filter

variable {a b e f : Type*}
  [Fintype a] [Fintype b] [Fintype e] [Fintype f]
  [DecidableEq a] [DecidableEq b] [DecidableEq e] [DecidableEq f]

/-- The fixed-block amplification theorem with its actual vanishing-approximation
premise. It holds already for a contraction target, hence for the paper's isometry. -/
theorem fixed_block_exponential
    (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ)
    (D : Matrix e f ℂ) (S L R : ℝ)
    (hVN : ‖VN‖ ≤ 1) (hexact : VN = applyEnvironment VM D)
    (hD : ‖D‖ ≤ (2 : ℝ) ^ (L / 2))
    (hvanish : VanishingAtRate VN VM S) (hSR : S < R) :
    ExponentialAtRate VN VM R := by
  by_cases hLR : L ≤ R
  · exact exponential_of_exact VN VM D L R hexact hD hLR
  have hRL : R < L := lt_of_not_ge hLR
  obtain ⟨η,hη,hη1,hmix⟩ := FixedBlockRates.exists_mixing_fraction hSR hRL
  let ε : ℝ := 1 / (1 + (4 : ℝ) ^ (1 / η))
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨l,_,hl,hblock,hgap⟩ := FixedBlockRates.choose_large_block (hvanish ε hε) hmix 0
  obtain ⟨C,hC,hCerror⟩ := hblock
  obtain ⟨Dl,hDl,hDlerror⟩ := exact_approxAt VN VM D L hexact hD l
  have hDlExact : blockDilation VN l = applyEnvironment (blockDilation VM l) Dl := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm hDlerror (norm_nonneg _)
  have hblocks (k : ℕ) : ∃ A : Matrix (Index e (l * k)) (Index f (l * k)) ℂ,
      ‖A‖ ≤ 3 ^ k * (2 : ℝ) ^ ((l : ℝ) * k * (S + η * (L - S)) / 2) ∧
      auxiliaryError VN VM (l * k) A ≤ (1 / 2 : ℝ) ^ k := by
    obtain ⟨A,hAnorm,hAerror⟩ := FixedBlockConstruction.fixed_block_auxiliary
      (blockDilation VN l) (blockDilation VM l) C Dl l k S L ε η
      (norm_blockDilation_le_one VN hVN l) hDlExact hCerror hε.le hη le_rfl
      (hSR.trans hRL).le hC hDl
    refine ⟨flattenAuxiliary l k A, ?_, ?_⟩
    · simpa only [norm_flattenAuxiliary] using hAnorm
    · rw [auxiliaryError_flattenAuxiliary]
      exact hAerror
  refine ⟨2, Real.log 2 / (l : ℝ), by norm_num,
    FixedBlockRates.fixed_block_decay_rate_pos l hl, ?_⟩
  filter_upwards [FixedBlockRates.eventually_padded_retained_cost_mul_le l hl (L := L) hgap]
    with N hcost
  obtain ⟨A,hAnorm,hAerror⟩ := hblocks (N / l)
  obtain ⟨Dq,hDq,hDqerror⟩ := exact_approxAt VN VM D L hexact hD (N % l)
  have hDqExact : blockDilation VN (N % l) = applyEnvironment (blockDilation VM (N % l)) Dq := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm hDqerror (norm_nonneg _)
  have hresult : ApproxAt VN VM (l * (N / l) + N % l) R
      (2 * Real.exp (-(Real.log 2 / (l : ℝ)) * (N : ℝ))) := by
    refine ⟨padAuxiliary (l * (N / l)) (N % l) A Dq, ?_, ?_⟩
    · have hnorm := (norm_padAuxiliary_le _ _ A Dq).trans
        (mul_le_mul hAnorm hDq (norm_nonneg _) (by positivity))
      simpa only [Nat.div_add_mod] using hnorm.trans hcost
    · exact (auxiliaryError_padAuxiliary_le VN VM _ _ A Dq hDqExact
        (norm_blockDilation_le_one VN hVN (N % l))).trans
        (hAerror.trans (FixedBlockRates.half_pow_div_le_exponential N l hl))
  simpa only [Nat.div_add_mod] using hresult

/-- **Lemma 4.5 (Fixed-block exponential amplification).** A concrete family
of auxiliary matrices at rate S with errors tending to zero yields exponential
uniform approximation at every strictly larger rate. This includes the
prescribed Stinespring-isometry setting and its exact residual map. -/
theorem lemma_4_5
    (VN : Matrix (b × e) a ℂ) (VM : Matrix (b × f) a ℂ)
    (D : Matrix e f ℂ) (S L R : ℝ)
    (hVN : VNᴴ * VN = 1) (hexact : VN = applyEnvironment VM D)
    (hD : ‖D‖ ≤ (2 : ℝ) ^ (L / 2))
    (A : (k : ℕ) → Matrix (Index e k) (Index f k) ℂ)
    (hrate : ∀ᶠ k : ℕ in atTop, ‖A k‖ ≤ (2 : ℝ) ^ ((k : ℝ) * S / 2))
    (herror : Tendsto (fun k => auxiliaryError VN VM k (A k)) atTop (𝓝 0))
    (hSR : S < R) : ExponentialAtRate VN VM R :=
  fixed_block_exponential VN VM D S L R (norm_isometry_le_one VN hVN) hexact hD
    (vanishing_of_family VN VM S A hrate herror) hSR

end QuantumChannelStein.ExponentialAmplification
