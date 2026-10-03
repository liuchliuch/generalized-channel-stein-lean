import GeneralizedChannelStein.Families
import QuantumChannelStein.ChannelComposition
import QuantumChannelStein.TensorPermutation
import QuantumChannelStein.TensorUnit

/-! Literal operations and the two extra hypotheses of Definition 14.
Kraus witnesses quantify over every actual CPTP map by `isChannel_iff_kraus`.
They do not impose compactness on the space of Kraus representations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelPowerReindex PerfectDiscrimination Matrix
open scoped Kronecker BigOperators ComplexOrder

/-- The unique normalized one-dimensional state. -/
def scalarState : State 1 where
  matrix := 1
  positive := Matrix.PosSemidef.one
  trace_one := by simp

/-- Prepare a fixed state at the right of an otherwise untouched input. -/
def appendState (d : ℕ) {a : ℕ} (τ : State a) : KrausChannel d (d*a) :=
  reindexChannel (finCongr (Nat.mul_one d)) (Equiv.refl _)
    ((KrausChannel.identity d).tensor (ReplacerChannel.channel 1 τ))

theorem appendState_apply (d : ℕ) {a : ℕ} (τ : State a) (X : Operator d) :
    (appendState d τ).apply X =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ τ.matrix) := by
  have h := reindexChannel_apply (finCongr (Nat.mul_one d)) (Equiv.refl _)
    ((KrausChannel.identity d).tensor (ReplacerChannel.channel 1 τ))
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ (1 : Operator 1)))
  rw [reindex_tensor_one, KrausChannel.tensor_apply_product, KrausChannel.identity_apply,
    ReplacerChannel.channel_apply] at h
  simpa using h

/-- Discard the last tensor factor, leaving the first factor unchanged. -/
def discardRight (d b : ℕ) : KrausChannel (d*b) d :=
  reindexChannel (Equiv.refl _) (finCongr (Nat.mul_one d))
    ((KrausChannel.identity d).tensor (ReplacerChannel.channel b scalarState))

theorem discardRight_apply_product (d b : ℕ) (X : Operator d) (Y : Operator b) :
    (discardRight d b).apply (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y)) =
      Y.trace • X := by
  have h := reindexChannel_apply (Equiv.refl _) (finCongr (Nat.mul_one d))
    ((KrausChannel.identity d).tensor (ReplacerChannel.channel b scalarState))
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ Y))
  simp only [Matrix.reindex_refl_refl, KrausChannel.tensor_apply_product,
    KrausChannel.identity_apply, ReplacerChannel.channel_apply, scalarState] at h
  rw [Matrix.kronecker_smul, ← Matrix.smul_kronecker, reindex_tensor_one] at h
  exact h

/-- On arbitrary, including entangled, operators this is exactly partial trace. -/
theorem discardRight_apply (d b : ℕ)
    (Y : Matrix (Fin d × Fin b) (Fin d × Fin b) ℂ) :
    (discardRight d b).apply (Matrix.reindex finProdFinEquiv finProdFinEquiv Y) =
      fun i j => ∑ l : Fin b, Y (i,l) (j,l) := by
  let X : Operator d := fun i j => ∑ l : Fin b, Y (i,l) (j,l)
  have h := reindexChannel_apply (Equiv.refl _) (finCongr (Nat.mul_one d))
    ((KrausChannel.identity d).tensor (ReplacerChannel.channel b scalarState))
    (Matrix.reindex finProdFinEquiv finProdFinEquiv Y)
  simp only [Matrix.reindex_refl_refl,ChannelLocality.identity_tensor_apply_reindex] at h
  have he : (ReplacerChannel.channel b scalarState).amplify d Y = X ⊗ₖ (1:Operator 1) := by
    rw [← MatrixMap.amplify_toLinearMap,ReplacerChannel.channel_map]
    ext ⟨i,k⟩ ⟨j,l⟩
    simp [MatrixMap.amplify,ReplacerChannel.linearMap,scalarState,X,Matrix.trace,Matrix.diag]
  rw [he,reindex_tensor_one] at h
  exact h

/-- Site permutation on the canonical flattened coordinates used for channel powers. -/
def sitePermutation (d n : ℕ) (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (d^n)) :=
  (channelIndexEquiv d n).symm.trans
    ((TensorPermutation.factorPermutation (Fin d) n π).trans (channelIndexEquiv d n))

theorem statePower_permutation {d : ℕ} (τ : State d) (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Matrix.reindex (sitePermutation d n π) (sitePermutation d n π) (statePower τ n).matrix =
      (statePower τ n).matrix := by
  have h := TensorPermutation.tensorPower_permutation τ.matrix n π
  ext i j
  simpa [statePower, sitePermutation, Matrix.reindex_apply] using
    congrFun (congrFun h ((channelIndexEquiv d n).symm i)) ((channelIndexEquiv d n).symm j)

/-- Simultaneous permutation of the input and output sites (F4). -/
def permuteChannel {a b : ℕ} (n : ℕ) (π : Equiv.Perm (Fin n))
    (Φ : KrausChannel (a^n) (b^n)) : KrausChannel (a^n) (b^n) :=
  reindexChannel (sitePermutation a n π) (sitePermutation b n π) Φ

/-- Insert the same single-copy state and discard the corresponding output (F5).
The one-copy `statePower` only transports coordinates to the n+1 block convention. -/
def marginalChannel {a b : ℕ} (n : ℕ) (τ : State a)
    (Φ : KrausChannel (a^(n+1)) (b^(n+1))) : KrausChannel (a^n) (b^n) :=
  (discardRight (b^n) (b^1)).compose
    ((reindexChannel (channelAddEquiv a n 1).symm (channelAddEquiv b n 1).symm Φ).compose
      (appendState (a^n) (statePower τ 1)))

/-- F4 and F5 with their actual witnessing input state fixed explicitly. -/
structure QuantitativeAt {a b : ℕ} (F : AlternativeFamily a b) (τ : State a) : Prop where
  faithful : τ.matrix.PosDef
  permutation_closed : ∀ n, 0 < n → ∀ π : Equiv.Perm (Fin n),
    ∀ Φ : KrausChannel (a^n) (b^n), Φ.toLinearMap ∈ F n →
      (permuteChannel n π Φ).toLinearMap ∈ F n
  marginal_closed : ∀ n, 0 < n → ∀ Φ : KrausChannel (a^(n+1)) (b^(n+1)),
    Φ.toLinearMap ∈ F (n+1) → (marginalChannel n τ Φ).toLinearMap ∈ F n

/-- Definition 14 adds only these two conditions to Definition 1. -/
def QuantitativeConditions {a b : ℕ} (F : AlternativeFamily a b) : Prop :=
  ∃ τ : State a, QuantitativeAt F τ


/-- Repeated last-site insertion/discarding, with the retained block nonempty. -/
def iteratedMarginal {a b : ℕ} (n : ℕ) (τ : State a) :
    (m : ℕ) → KrausChannel (a^(n+m)) (b^(n+m)) → KrausChannel (a^n) (b^n)
  | 0, Φ => Φ
  | m+1, Φ => iteratedMarginal n τ m (marginalChannel (n+m) τ Φ)

theorem QuantitativeAt.iterated_marginal_closed {a b : ℕ} {F : AlternativeFamily a b}
    {τ : State a} (hF : QuantitativeAt F τ) (n m : ℕ) (hn : 0<n)
    (Φ : KrausChannel (a^(n+m)) (b^(n+m))) (hΦ : Φ.toLinearMap ∈ F (n+m)) :
    (iteratedMarginal n τ m Φ).toLinearMap ∈ F n := by
  induction m with
  | zero => exact hΦ
  | succ m ih =>
    exact ih _ (hF.marginal_closed (n+m) (by omega) Φ hΦ)

end GeneralizedChannelStein
