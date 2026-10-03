import QuantumChannelStein.ReplacerChannel
import QuantumChannelStein.ParallelTestingReduction
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Literal finite-dimensional alternative families

The family is a set of complex-linear maps, not a set of Kraus presentations.
Compactness and convexity therefore refer to the actual finite-dimensional
channel space. Tensor closure uses the same coordinate identification for all
channels. No symmetry or marginal closure enters `Admissible`.
-/
noncomputable section
namespace GeneralizedChannelStein
open QuantumChannelStein
open ChannelEntropy ChannelPowerReindex
open scoped ComplexOrder

variable {a b : ℕ}

/-- Exact CPTP, with complete positivity quantified over every finite reference. -/
def IsChannel (Φ : MatrixMap a b) : Prop :=
  MatrixMap.CompletelyPositive Φ ∧ ∀ X, (Φ X).trace = X.trace

/-- No channel is omitted by using finite Kraus witnesses in optimizations. -/
theorem isChannel_iff_kraus (Φ : MatrixMap a b) :
    IsChannel Φ ↔ ∃ K : KrausChannel a b, K.toLinearMap = Φ :=
  MatrixMap.cptp_iff_exists_kraus Φ

/-- Actual sets of block-channel linear maps. The zero block is unused. -/
abbrev AlternativeFamily (a b : ℕ) := (n : ℕ) → Set (MatrixMap (a^n) (b^n))

/-- Tensor two blocks, identifying their coordinates with the sum block. -/
def tensorBlocks (n m : ℕ) (Φ : KrausChannel (a^n) (b^n))
    (Ψ : KrausChannel (a^m) (b^m)) : KrausChannel (a^(n+m)) (b^(n+m)) :=
  reindexChannel (channelAddEquiv a n m) (channelAddEquiv b n m) (Φ.tensor Ψ)

/-- Definition 1, precisely F1--F3. Witness faithfulness is positive definiteness. -/
structure Admissible (F : AlternativeFamily a b) : Prop where
  channels : ∀ n, 0 < n → ∀ Φ ∈ F n, IsChannel Φ
  nonempty : ∀ n, 0 < n → (F n).Nonempty
  compact : ∀ n, 0 < n → IsCompact (MatrixMap.choi '' F n)
  convex : ∀ n, 0 < n → Convex ℝ (MatrixMap.choi '' F n)
  tensor_closed : ∀ n m, 0 < n → 0 < m →
    ∀ (Φ : KrausChannel (a^n) (b^n)) (Ψ : KrausChannel (a^m) (b^m)),
      Φ.toLinearMap ∈ F n → Ψ.toLinearMap ∈ F m →
        (tensorBlocks n m Φ Ψ).toLinearMap ∈ F (n+m)
  faithful_replacer : ∃ ω : State b, ω.matrix.PosDef ∧
    ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1

/-- Tensor closure promotes exactly the F3 one-use witness to every positive block. -/
theorem replacer_power_mem (F : AlternativeFamily a b)
    (hTensor : ∀ n m, 0 < n → 0 < m →
      ∀ (Φ : KrausChannel (a^n) (b^n)) (Ψ : KrausChannel (a^m) (b^m)),
      Φ.toLinearMap ∈ F n → Ψ.toLinearMap ∈ F m →
      (tensorBlocks n m Φ Ψ).toLinearMap ∈ F (n+m))
    (ω : State b)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1) :
    ∀ n, 0 < n → ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ F n := by
  intro n hn
  induction n using Nat.case_strong_induction_on with
  | hz => omega
  | hi n ih =>
    by_cases hzero : n = 0
    · subst n
      exact hOne
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
      have h := hTensor n 1 hnpos (by omega)
        ((ReplacerChannel.channel a ω).tensorPower n)
        ((ReplacerChannel.channel a ω).tensorPower 1)
        (ih n (Nat.le_refl n) hnpos) hOne
      simpa only [tensorBlocks, tensorPower_add_toLinearMap] using h

/-- Admissibility supplies a single faithful state across every blocklength. -/
theorem Admissible.exists_replacer_powers (F : AlternativeFamily a b)
    (hF : Admissible F) :
    ∃ ω : State b, ω.matrix.PosDef ∧ ∀ n, 0 < n →
      ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ F n := by
  obtain ⟨ω,hω,hm⟩ := hF.faithful_replacer
  exact ⟨ω,hω,replacer_power_mem F hF.tensor_closed ω hm⟩

end GeneralizedChannelStein
