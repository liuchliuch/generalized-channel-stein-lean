import GeneralizedChannelStein.QuantitativeCompletionBridge
import GeneralizedChannelStein.IsometricCompletion

/-! # Theorem 16: uniform free-channel domination for every quantum channel -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- Depends only on dimensions, the two lower eigenvalues, and the fixed testing tolerance. -/
def generalCompletionConstant (a b : ℕ) (t w ε : ℝ) : ℝ :=
  CompletionPrefactor.adjustedConstant
    (IsometricCompletion.uniformConstant a (b*(a*b)) t (w/(a*b:ℕ)) (completionOverlap ε))
    (ExtensionComparison.factor ε)

/-- The constant is fixed before the target, family, states, blocklength, or accuracy. -/
theorem theorem_16_uniform_lowerBounds (ha : 0<a) (hb : 0<b)
    (t w ε : ℝ) (ht : 0<t) (ht1 : t≤1) (hw : 0<w) (hw1 : w≤1)
    (hε : 0<ε) (hε1 : ε<1) :
    ∀ (N : KrausChannel a b) (F : AlternativeFamily a b), Admissible F →
    ∀ (τ : State a), QuantitativeAt F τ → ∀ (ω : State b), ω.matrix.PosDef →
    ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1 →
    (τ.matrix-t•(1:Operator a)).PosSemidef → (ω.matrix-w•(1:Operator b)).PosSemidef →
    CompletionProperty N F ε (generalCompletionConstant a b t w ε) := by
  have he : 0<a*b := Nat.mul_pos ha hb
  have he1 : (1:ℝ)≤(a*b:ℕ) := by exact_mod_cast he
  have hwe : 0<w/(a*b:ℕ) := div_pos hw (by exact_mod_cast he)
  have hwe1 : w/(a*b:ℕ)≤1 := (div_le_one (by exact_mod_cast he)).mpr (hw1.trans he1)
  have hIso := IsometricCompletion.property_of_le_one ha (Nat.mul_pos hb he)
    t (w/(a*b:ℕ)) (completionOverlap ε) ht ht1 hwe hwe1
    (completionOverlap_pos ε hε hε1) (completionOverlap_le_one ε)
  intro N F hF τ hQ ω hω hOne hτt hωw
  exact completion_of_isometric_property ha hb t w ε _ hε hε1 hIso N F hF τ hQ ω hω hOne hτt hωw

/-- Theorem 16 with actual minimum eigenvalues and no completion oracle premise. -/
theorem theorem_16 (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (τ : State a) (hQ : QuantitativeAt F τ)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    CompletionProperty N F ε (generalCompletionConstant a b
      (DimensionDomination.minEigenvalue τ ha) (DimensionDomination.minEigenvalue ω hb) ε) := by
  apply theorem_16_uniform_lowerBounds ha hb
    (DimensionDomination.minEigenvalue τ ha) (DimensionDomination.minEigenvalue ω hb) ε
    (DimensionDomination.minEigenvalue_pos τ ha hQ.faithful)
    (DimensionDomination.minEigenvalue_le_one τ ha)
    (DimensionDomination.minEigenvalue_pos ω hb hω)
    (DimensionDomination.minEigenvalue_le_one ω hb) hε hε1 N F hF τ hQ ω hω hOne
  · exact DimensionDomination.scalar_le_of_eigenvalue_lower τ _ (DimensionDomination.minEigenvalue_le τ ha)
  · exact DimensionDomination.scalar_le_of_eigenvalue_lower ω _ (DimensionDomination.minEigenvalue_le ω hb)

/-- Existential paper presentation, with all permitted radii and every positive integer block. -/
theorem theorem_16_exists (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (hQ : QuantitativeConditions F)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) : ∃ K : ℝ, CompletionProperty N F ε K := by
  obtain ⟨τ,hτ⟩ := hQ
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  exact ⟨_,theorem_16 N ha hb F hF τ hτ ω hω hOne ε hε hε1⟩

end GeneralizedChannelStein
