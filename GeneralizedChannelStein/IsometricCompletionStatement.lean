import GeneralizedChannelStein.CompletionStatement
import GeneralizedChannelStein.IsometricBenchmarks
import GeneralizedChannelStein.BranchExtraction

/-! The literal uniform input/output contract of Proposition 30. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- K is fixed before the free family, witness states, isometry, block length,
accuracy, branch, and original domination coefficient are chosen. -/
structure IsometricCompletionProperty (a d : ℕ) (t w c K : ℝ) : Prop where
  nonnegative : 0≤K
  complete : ∀ (F : AlternativeFamily a d), Admissible F →
    ∀ (τ : State a), QuantitativeAt F τ → ∀ (ω : State d),
    ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1 →
    (τ.matrix-t•(1:Operator a)).PosSemidef → (ω.matrix-w•(1:Operator d)).PosSemidef →
    ∀ (J : Matrix (Fin d) (Fin a) ℂ) (hJ : Jᴴ*J=1) (n : ℕ), 0<n →
    ∀ (M : KrausChannel (a^n) (d^n)), M.toLinearMap∈F n →
    ∀ (V : Matrix (Fin (d^n)) (Fin (a^n)) ℂ) (p : ℝ), 0<p → p≤1 → ‖V‖≤1 →
    (BranchExtraction.realPart ((powerIsometry J n)ᴴ*V)-c•1).PosSemidef →
    MatrixMap.CPLe (Complex.ofReal p•BranchExtraction.adMap V) M.toLinearMap →
    ∀ (δ : ℝ), 0<δ → δ≤1/16 →
    ∃ L S : KrausChannel (a^n) (d^n), S.toLinearMap∈F n ∧
      MatrixMap.CPLe (Complex.ofReal (p*(2:ℝ)^(-completionLoss K n δ))•L.toLinearMap) S.toLinearMap ∧
      DiamondNorm.diamondNorm (L.toLinearMap-BranchExtraction.adMap (powerIsometry J n))≤ENNReal.ofReal δ

end GeneralizedChannelStein
