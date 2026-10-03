import GeneralizedChannelStein.EntropyLimit

/-! # Theorems 2 and 3 of arXiv:2609.30762v1

These endpoints use only actual finite-dimensional channels and F1--F3.
All testing, approximation, entropy comparison, and limit bridges are proved
in the imported dependency chain, with no conclusion supplied as a premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DiamondNorm Filter
open scoped Topology ComplexOrder
variable {a b : ℕ}

/-- **Theorem 2:** the ordinary fixed-error testing and optimized Umegaki
entropy limits coincide, with a finite nonnegative rate and the paper's bound. -/
theorem theorem_2 (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → Tendsto (testingRateReal N F ε) atTop (𝓝 R)) ∧
      Tendsto (entropyRateReal N F) atTop (𝓝 R) ∧
      (∀ ω : State b, ω.matrix.PosDef →
        ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1 →
        R ≤ replacerRate ω hb) :=
  ⟨steinRate N F,steinRate_nonneg N ha F,
    testing_limit N ha hb F hF,entropy_limit N ha hb F hF,
    fun ω hω hOne => steinRate_le_replacerRate N ha hb F hF ω hω hOne⟩

/-- **Theorem 3:** one exactly trace-preserving approximation and one free
CP dominator for each sufficiently large n, with constants chosen before n.
The full diamond norm makes the same witnesses uniform over every reference,
input and test, rather than allowing input-dependent approximations. -/
theorem theorem_3 (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (S : ℝ) (hS : steinRate N F < S) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ L M : KrausChannel (a^n) (b^n), M.toLinearMap ∈ F n ∧
        MatrixMap.CPLe L.toLinearMap (Complex.ofReal ((2:ℝ)^((n:ℝ)*S)) • M.toLinearMap) ∧
        diamondNorm (L.toLinearMap-(N.tensorPower n).toLinearMap) ≤
          ENNReal.ofReal (K*Real.exp (-γ*(n:ℝ))) := by
  obtain ⟨K,γ,hK,hγ,h⟩ := exponential_above_steinRate N ha hb F hF S hS
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp h
  exact ⟨K,γ,hK,hγ,n₀,hn₀⟩

end GeneralizedChannelStein
