import GeneralizedChannelStein.Smoothing

/-! # Literal statement of the quantitative exact-TP completion bound -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein DiamondNorm

/-- The exact completion overhead, in bits. -/
def completionLoss (K : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  K * (n : ℝ)^((2:ℝ)/3) * Real.logb 2 (((n:ℝ)+1)/δ)

/-- Concrete witnesses at every positive blocklength and permitted diamond radius.
This is an intermediate statement, not an axiom or an assumed numbered result. -/
structure CompletionProperty {a b : ℕ} (N : KrausChannel a b)
    (F : AlternativeFamily a b) (ε K : ℝ) : Prop where
  constant_nonneg : 0 ≤ K
  complete : ∀ n : ℕ, 0<n → ∀ δ : ℝ, 0<δ → δ≤1/16 →
    ∃ L S : KrausChannel (a^n) (b^n), S.toLinearMap ∈ F n ∧
      MatrixMap.CPLe
        (Complex.ofReal ((compositeBeta (N.tensorPower n) (F n) ε).toReal *
          (2:ℝ)^(-completionLoss K n δ)) • L.toLinearMap) S.toLinearMap ∧
      diamondNorm (L.toLinearMap-(N.tensorPower n).toLinearMap) ≤ ENNReal.ofReal δ

end GeneralizedChannelStein
