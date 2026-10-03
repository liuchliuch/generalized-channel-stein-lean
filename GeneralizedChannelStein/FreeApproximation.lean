import GeneralizedChannelStein.Families
import QuantumChannelStein.DiamondNorm

/-! # Transparent predicates for exact-TP free-channel approximation -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein DiamondNorm
open scoped Topology

/-- Concrete normalized approximant and one input-independent free dominator. -/
def FreeApproxAt {a b : ℕ} (N : KrausChannel a b) (F : AlternativeFamily a b)
    (n : ℕ) (R δ : ℝ) : Prop :=
  ∃ L S : KrausChannel (a^n) (b^n), S.toLinearMap ∈ F n ∧
    MatrixMap.CPLe L.toLinearMap (Complex.ofReal ((2 : ℝ) ^ ((n : ℝ) * R)) • S.toLinearMap) ∧
    diamondNorm (L.toLinearMap - (N.tensorPower n).toLinearMap) ≤ ENNReal.ofReal δ

/-- Positive constants chosen before all sufficiently large blocklengths. -/
def ExponentialFreeApprox {a b : ℕ} (N : KrausChannel a b) (F : AlternativeFamily a b)
    (R : ℝ) : Prop :=
  ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ ∀ᶠ n : ℕ in Filter.atTop,
    FreeApproxAt N F n R (K * Real.exp (-γ * (n : ℝ)))

/-- Arbitrarily late normalized approximations at every strictly larger rate
and arbitrarily small error, with an actual free dominator at each chosen block. -/
def VanishingFreeApprox {a b : ℕ} (N : KrausChannel a b) (F : AlternativeFamily a b)
    (r₀ : ℝ) : Prop :=
  ∀ r : ℝ, r₀ < r → ∀ δ : ℝ, 0 < δ → ∀ k₀ : ℕ,
    ∃ k : ℕ, k₀ ≤ k ∧ 0 < k ∧ FreeApproxAt N F k r δ

end GeneralizedChannelStein
