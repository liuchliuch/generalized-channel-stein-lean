import GeneralizedChannelStein.SymmetricLargeError
import GeneralizedChannelStein.SymmetricHardest
import GeneralizedChannelStein.LargeErrorScalars

/-! # Lemma 33: symmetric large-error bound with the literal binomial overhead

Only F1–F4 are used. The fixed faithful replacer is the F3 witness;
no marginal closure, supplied optimizer, or spectral-count assumption occurs.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.NearSubadditiveEntropy
open QuantumChannelStein ChannelEntropy
open scoped ComplexOrder
variable {a b : ℕ}

/-- Paper Lemma 33, with the witnessing F3 state and the exact finite-block quantities. -/
theorem lemma_33 (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0<n)
    (hperm : ∀ π : Equiv.Perm (Fin n), ∀ M : KrausChannel (a^n) (b^n),
      M.toLinearMap ∈ F n → (permuteChannel n π M).toLinearMap ∈ F n)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ((familyEntropy (N.tensorPower n) (F n)).toReal -
      (1-ε)*((n:ℝ)*replacerRate ω hb+1) -
      Real.logb 2 (((n+(a*b)^2-1).choose ((a*b)^2-1) : ℕ) : ℝ))/ε - 1 ≤
        -Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal := by
  obtain ⟨M,hM,hβ,hMcov⟩ := SymmetricHardest.tensor_symmetric_hardest
    N ha F hF n hn hperm ε hε.le
  have hbound := SymmetricLargeError.singleBeta_le N ha hb F hF ω hω hOne
    n hn ε hε hε1 M hM hMcov
  rw [← hβ] at hbound
  have hfin := admissible_values_finite N ha hb F hF n hn ε hε hε1
  have hout := LargeErrorScalars.exponent_lower _ hfin.2.2.1 hfin.2.2.2 _ hbound
  convert hout using 1
  ring

/-- Equivalent entropy form, useful in the alternate ordinary-limit proof. -/
theorem lemma_33_entropy_form (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0<n)
    (hperm : ∀ π : Equiv.Perm (Fin n), ∀ M : KrausChannel (a^n) (b^n),
      M.toLinearMap ∈ F n → (permuteChannel n π M).toLinearMap ∈ F n)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    (familyEntropy (N.tensorPower n) (F n)).toReal ≤
      ε*(-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal) +
      (1-ε)*((n:ℝ)*replacerRate ω hb+1) +
      Real.logb 2 (((n+(a*b)^2-1).choose ((a*b)^2-1) : ℕ) : ℝ) + ε := by
  have h := lemma_33 N ha hb F hF ω hω hOne n hn hperm ε hε hε1
  have hm := mul_le_mul_of_nonneg_left h hε.le
  rw [mul_sub, mul_div_cancel₀ _ hε.ne'] at hm
  nlinarith

end GeneralizedChannelStein.NearSubadditiveEntropy
