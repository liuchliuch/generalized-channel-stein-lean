import QuantumChannelStein.UniformApproximationFromTesting
import QuantumChannelStein.ChannelTestingEntropyBound

/-!
# Theorem 2.2: exponential Stinespring approximation

This is the unconditional assembly from the actual entropy/data-processing
weak-testing theorem, the operational SDP and fixed-environment comparison,
and the proved two-rate and fixed-block tensor constructions.

The output is an actual family of rectangular matrices between the powers
of the originally prescribed environment spaces, with the literal norm
bound and an explicit sufficiently-large threshold. No weak-testing,
rate-improvement, or abstract tensor-power hypothesis remains.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ExponentialStinespring
open scoped BigOperators Kronecker Matrix.Norms.L2Operator Topology
open Matrix ChannelEntropy TensorPower EnvironmentTensor UniformApproximation
  ChannelDilationPower UniformApproximationFromTesting TestingPrimal Filter

variable {a b eN eM : ℕ}

/-- The genuine Lemma 4.3 discharges the last analytical premise of the
matrix amplification construction. -/
theorem exponentialAtRate_of_finite_regularizedD (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVNiso : VNᴴ * VN = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (hfinite : regularizedD Φ Ψ < ⊤) (S : ℝ)
    (hS : (regularizedD Φ Ψ).toReal < S) : ExponentialAtRate VN VM S := by
  have hbot : regularizedD Φ Ψ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (regularizedD_nonneg Φ Ψ ha))
  have hreg : regularizedD Φ Ψ = ((regularizedD Φ Ψ).toReal : EReal) :=
    (EReal.coe_toReal hfinite.ne hbot).symm
  apply exponential_of_regularized_weak_testing Φ Ψ ha VN VM hVNiso hVN hVM
    (regularizedD Φ Ψ).toReal S hreg hS
  intro r hdr
  have hd : 0 ≤ (regularizedD Φ Ψ).toReal := EReal.toReal_nonneg (regularizedD_nonneg Φ Ψ ha)
  have hr : 0 < r := hd.trans_lt hdr
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  exact (channelHockeyStick_tensorPower_le_finite Φ Ψ ha hfinite r hr k hk).trans
    (min_le_right _ _)

/-- An exponential approximation supplies a single actual operator family
with the literal unsquared norm bound from Theorem 2.2. -/
theorem exponentialAtRate_norm_family
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (S : ℝ)
    (h : ExponentialAtRate VN VM S) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧
      ∃ C : (k : ℕ) → Matrix (Fin (eN ^ k)) (Fin (eM ^ k)) ℂ,
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        ‖C k‖ ≤ (2 : ℝ) ^ ((k : ℝ) * S / 2) ∧
        ‖powerDilation VN k - ((1 : Operator (b ^ k)) ⊗ₖ C k) * powerDilation VM k‖ ≤
          K * Real.exp (-γ * k) := by
  classical
  obtain ⟨K, γ, hK, hγ, happrox⟩ := h
  let A : (k : ℕ) → Matrix (Index (Fin eN) k) (Index (Fin eM) k) ℂ := fun k =>
    if hk : ApproxAt VN VM k S (K * Real.exp (-γ * k)) then Classical.choose hk else 0
  have hA : ∀ᶠ k : ℕ in atTop,
      ‖A k‖ ≤ (2 : ℝ) ^ ((k : ℝ) * S / 2) ∧
      auxiliaryError VN VM k (A k) ≤ K * Real.exp (-γ * k) := by
    filter_upwards [happrox] with k hk
    dsimp [A]
    rw [dif_pos hk]
    exact Classical.choose_spec hk
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hA
  refine ⟨K, γ, hK, hγ, fun k => finiteAuxiliary k (A k), N, ?_⟩
  intro k hk
  have hAk := hN k hk
  constructor
  · simpa only [norm_finiteAuxiliary] using hAk.1
  · change ‖powerDilation VN k - applyEnvironment (powerDilation VM k) (finiteAuxiliary k (A k))‖ ≤ _
    rw [finiteAuxiliary_error]
    exact hAk.2

/-- **Theorem 2.2 (Exponential Stinespring approximation)** of
arXiv:2609.27196v1. The prescribed dilation tensors and the auxiliary family
are genuine matrices, with both rates and the eventual threshold explicit. -/
theorem theorem_2_2 (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVNiso : VNᴴ * VN = 1) (_hVMiso : VMᴴ * VM = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (hfinite : regularizedD Φ Ψ < ⊤) (S : ℝ)
    (hS : (regularizedD Φ Ψ).toReal < S) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧
      ∃ C : (k : ℕ) → Matrix (Fin (eN ^ k)) (Fin (eM ^ k)) ℂ,
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        ‖C k‖ ≤ (2 : ℝ) ^ ((k : ℝ) * S / 2) ∧
        ‖powerDilation VN k - ((1 : Operator (b ^ k)) ⊗ₖ C k) * powerDilation VM k‖ ≤
          K * Real.exp (-γ * k) :=
  exponentialAtRate_norm_family VN VM S
    (exponentialAtRate_of_finite_regularizedD Φ Ψ ha VN VM hVNiso hVN hVM hfinite S hS)

/-- The equivalent squared auxiliary-norm normalization used in later tests. -/
theorem theorem_2_2_squared (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVNiso : VNᴴ * VN = 1) (_hVMiso : VMᴴ * VM = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (hfinite : regularizedD Φ Ψ < ⊤) (S : ℝ)
    (hS : (regularizedD Φ Ψ).toReal < S) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧
      ∃ C : (k : ℕ) → Matrix (Fin (eN ^ k)) (Fin (eM ^ k)) ℂ,
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        ‖C k‖ ^ 2 ≤ (2 : ℝ) ^ ((k : ℝ) * S) ∧
        ‖powerDilation VN k - ((1 : Operator (b ^ k)) ⊗ₖ C k) * powerDilation VM k‖ ≤
          K * Real.exp (-γ * k) :=
  exponentialAtRate_finite_family VN VM S
    (exponentialAtRate_of_finite_regularizedD Φ Ψ ha VN VM hVNiso hVN hVM hfinite S hS)

end QuantumChannelStein.ExponentialStinespring
