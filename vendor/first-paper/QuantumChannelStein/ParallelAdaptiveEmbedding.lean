import QuantumChannelStein.AdaptiveCircuit
import QuantumChannelStein.SequentialTensor

/-! # Genuine sequential embedding of every parallel pure test -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein
open Matrix ChannelEntropy OperationalTesting
open scoped BigOperators Kronecker

namespace State
variable {u v w : ℕ}
@[simp] theorem reindex_refl (ρ : State u) : ρ.reindex (Equiv.refl _) = ρ := by
  apply State.eq_of_matrix_eq
  rfl

@[simp] theorem reindex_trans (ρ : State u) (e : Fin u ≃ Fin v) (f : Fin v ≃ Fin w) :
    (ρ.reindex e).reindex f = ρ.reindex (e.trans f) := by
  apply State.eq_of_matrix_eq
  rfl
end State

namespace AdaptiveProtocol
open SequentialTensor
variable {a b k r : ℕ}

/-- The input permutation exposes one original factor, leaving the others in memory. -/
def powerExpose (a r k : ℕ) : Fin (r * a ^ (k + 1)) ≃ Fin ((r * a ^ k) * a) :=
  (finCongr (congrArg (fun x => r * x) (@Nat.pow_succ' a k))).trans (expose r a (a ^ k))

/-- The output permutation collects the processed factors in the original tensor convention. -/
def powerCollect (b r k : ℕ) : Fin ((r * b) * b ^ k) ≃ Fin (r * b ^ (k + 1)) :=
  (collect r b (b ^ k)).trans (finCongr (congrArg (fun x => r * x) (@Nat.pow_succ' b k).symm))

/-- A circuit of exactly k individual channel calls, with only actual coordinate
controls. No control operation depends on which channel hypothesis is used. -/
def parallelCircuit (a b : ℕ) : (k r : ℕ) → Circuit a b k (r * a ^ k) (r * b ^ k)
  | 0, r => .control (KrausChannel.identity (r * 1))
  | k + 1, r => .query (KrausChannel.coordinateChange (powerExpose a r k))
      (((parallelCircuit a b k (r * b)).precompose
        (KrausChannel.coordinateChange (storeOutput r (a ^ k) b))).postcompose
          (KrausChannel.coordinateChange (powerCollect b r k)))

/-- Mixed reference-assisted outputs respect the literal dimension transports. -/
theorem outputState_cast_from {a' b' : ℕ} (Φ : KrausChannel a b)
    (ha : a = a') (hb : b = b') (r : ℕ) (ρ : State (r * a')) :
    outputState (Φ.cast ha hb) r ρ =
      (outputState Φ r (ρ.reindex (finCongr (congrArg (fun x => r * x) ha.symm)))).reindex
        (finCongr (congrArg (fun x => r * x) hb)) := by
  cases ha
  cases hb
  simp [KrausChannel.cast]

/-- Running the sequential circuit is exactly the actual tensor-power map,
even on an arbitrary entangled mixed reference/input state. -/
theorem parallelCircuit_run (Φ : KrausChannel a b) (k r : ℕ) (ρ : State (r * a ^ k)) :
    (parallelCircuit a b k r).run Φ ρ = outputState (Φ.tensorPower k) r ρ := by
  induction k generalizing r with
  | zero =>
    apply State.eq_of_matrix_eq
    simp [parallelCircuit, Circuit.run, KrausChannel.tensorPower, outputState,
      KrausChannel.amplify, KrausChannel.identity, KrausChannel.onState, KrausChannel.apply,
      Matrix.reindex_apply]
  | succ k ih =>
    simp only [parallelCircuit, Circuit.run, Circuit.run_postcompose, Circuit.run_precompose,
      KrausChannel.coordinateChange_onState]
    rw [ih]
    let e : Fin (r * a ^ (k + 1)) ≃ Fin (r * (a * a ^ k)) :=
      finCongr (congrArg (fun x => r * x) (@Nat.pow_succ' a k))
    have hs := sequentialChannel_onState Φ (Φ.tensorPower k) (ρ.reindex e)
    simp only [sequentialChannel, KrausChannel.compose_onState,
      KrausChannel.coordinateChange_onState, ← ChannelLocality.outputState_eq_tensor] at hs
    have hh := congrArg (fun X : State (r * (b * b ^ k)) =>
      X.reindex (finCongr (congrArg (fun x => r * x) (@Nat.pow_succ' b k).symm))) hs
    simp only [State.reindex_trans] at hh
    rw [KrausChannel.tensorPower, outputState_cast_from]
    exact hh

/-- The actual finite-memory protocol implementing a paper parallel pure test. -/
def parallelProtocol (k : ℕ) (ψ : UnitPureInput (a ^ k) (a ^ k))
    (T : Effect (a ^ k * b ^ k)) : Protocol a b k :=
  (parallelCircuit a b k (a ^ k)).toSkeleton.toProtocol (pureInputState ψ) T

/-- Exact equality of Born probabilities for every channel, not merely a bound. -/
theorem parallelProtocol_acceptance (Φ : KrausChannel a b) (k : ℕ)
    (ψ : UnitPureInput (a ^ k) (a ^ k)) (T : Effect (a ^ k * b ^ k)) :
    (parallelProtocol k ψ T).acceptance Φ = T.probability (pureOutput (Φ.tensorPower k) ψ) := by
  rw [parallelProtocol, Circuit.compile_acceptance, parallelCircuit_run]
  congr 1
  apply State.eq_of_matrix_eq
  exact outputState_pureInputState_matrix (Φ.tensorPower k) ψ

/-- Every paper parallel test is realized by one common actual adaptive strategy,
with both null and alternative probabilities preserved exactly. -/
theorem exists_parallel_protocol (Φ Ψ : KrausChannel a b) (k : ℕ)
    (ψ : UnitPureInput (a ^ k) (a ^ k)) (T : Effect (a ^ k * b ^ k)) :
    ∃ P : Protocol a b k,
      P.acceptance Φ = T.probability (pureOutput (Φ.tensorPower k) ψ) ∧
      P.acceptance Ψ = T.probability (pureOutput (Ψ.tensorPower k) ψ) :=
  ⟨parallelProtocol k ψ T, parallelProtocol_acceptance Φ k ψ T, parallelProtocol_acceptance Ψ k ψ T⟩

end AdaptiveProtocol
end QuantumChannelStein
