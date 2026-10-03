import QuantumChannelStein.AdaptiveProtocol
import QuantumChannelStein.ChannelComposition

/-! # Compiling genuine finite query circuits into adaptive protocols -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein
open Matrix OperationalTesting
open scoped BigOperators ComplexOrder

namespace KrausChannel
variable {u v : ℕ}

@[simp] theorem identity_onState (ρ : State u) : (identity u).onState ρ = ρ := by
  apply State.eq_of_matrix_eq
  exact identity_apply u ρ.matrix

/-- The genuine Heisenberg pullback of a binary effect through a CPTP map. -/
def pullbackEffect (C : KrausChannel u v) (T : Effect v) : Effect u where
  matrix := ∑ i, (C.kraus i)ᴴ * T.matrix * C.kraus i
  positive := by
    apply Finset.sum_induction
    · exact fun A B hA hB => hA.add hB
    · exact Matrix.PosSemidef.zero
    · intro i _
      exact T.positive.conjTranspose_mul_mul_same _
  complement_positive := by
    have heq : 1 - ∑ i, (C.kraus i)ᴴ * T.matrix * C.kraus i =
        ∑ i, (C.kraus i)ᴴ * (1 - T.matrix) * C.kraus i := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Finset.sum_sub_distrib, C.normalized]
    rw [heq]
    apply Finset.sum_induction
    · exact fun A B hA hB => hA.add hB
    · exact Matrix.PosSemidef.zero
    · intro i _
      exact T.complement_positive.conjTranspose_mul_mul_same _

/-- Pulling back the effect exactly preserves its actual Born probability. -/
theorem pullbackEffect_probability (C : KrausChannel u v) (T : Effect v) (ρ : State u) :
    (C.pullbackEffect T).probability ρ = T.probability (C.onState ρ) := by
  simp only [Effect.probability, pullbackEffect, onState, apply, Matrix.sum_mul,
    Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [show (C.kraus i)ᴴ * T.matrix * C.kraus i * ρ.matrix =
      (C.kraus i)ᴴ * (T.matrix * (C.kraus i * ρ.matrix)) by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end KrausChannel

namespace AdaptiveProtocol
variable {a b n u v r : ℕ}

/-- A syntax of actual finite CPTP controls and individual channel calls. -/
inductive Circuit (a b : ℕ) : ℕ → ℕ → ℕ → Type
  | control {u v : ℕ} (C : KrausChannel u v) : Circuit a b 0 u v
  | query {n u v r : ℕ} (before : KrausChannel u (r * a))
      (rest : Circuit a b n (r * b) v) : Circuit a b (n + 1) u v

/-- Actual state semantics, applying exactly one selected channel at each query. -/
def Circuit.run : {n u v : ℕ} → Circuit a b n u v → KrausChannel a b → State u → State v
  | _, _, _, .control D, _, ρ => D.onState ρ
  | _, _, _, .query B rest, Φ, ρ => rest.run Φ (outputState Φ _ (B.onState ρ))

/-- Append a genuine CPTP control to a finite circuit. -/
def Circuit.postcompose : {n u v v' : ℕ} → Circuit a b n u v → KrausChannel v v' → Circuit a b n u v'
  | _, _, _, _, .control E, D => .control (D.compose E)
  | _, _, _, _, .query B rest, D => .query B (rest.postcompose D)

@[simp] theorem Circuit.run_postcompose (C : Circuit a b n u v) {v' : ℕ}
    (D : KrausChannel v v') (Φ : KrausChannel a b) (ρ : State u) :
    (C.postcompose D).run Φ ρ = D.onState (C.run Φ ρ) := by
  induction C with
  | control E => exact KrausChannel.compose_onState D E ρ
  | query B rest ih => exact ih D (outputState Φ _ (B.onState ρ))

/-- Prepend a genuine CPTP control to a finite circuit. -/
def Circuit.precompose (C : Circuit a b n u v) {u' : ℕ} (D : KrausChannel u' u) :
    Circuit a b n u' v :=
  match C with
  | .control E => .control (E.compose D)
  | .query B rest => .query (B.compose D) rest

@[simp] theorem Circuit.run_precompose (C : Circuit a b n u v) {u' : ℕ}
    (D : KrausChannel u' u) (Φ : KrausChannel a b) (ρ : State u') :
    (C.precompose D).run Φ ρ = C.run Φ (D.onState ρ) := by
  cases C with
  | control E => exact KrausChannel.compose_onState E D ρ
  | query B rest => simp only [precompose, run, KrausChannel.compose_onState]

/-- A state-independent finite control skeleton, to be initialized and measured later. -/
structure Skeleton (a b n u v : ℕ) where
  memory : Fin (n + 1) → ℕ
  reference : Fin n → ℕ
  start : KrausChannel u (memory 0)
  before : (j : Fin n) → KrausChannel (memory j.castSucc) (reference j * a)
  after : (j : Fin n) → KrausChannel (reference j * b) (memory j.succ)
  finish : KrausChannel (memory (Fin.last n)) v

/-- Initialization and pulled-back final measurement produce an actual Protocol. -/
def Skeleton.toProtocol (S : Skeleton a b n u v) (ρ : State u) (T : Effect v) : Protocol a b n where
  memory := S.memory
  reference := S.reference
  initial := S.start.onState ρ
  before := S.before
  after := S.after
  effect := S.finish.pullbackEffect T

/-- Prepend one actual channel use to a state-independent skeleton. -/
def Skeleton.prepend (S : Skeleton a b n (r * b) v) (B : KrausChannel u (r * a)) :
    Skeleton a b (n + 1) u v where
  memory := Fin.cases u S.memory
  reference := Fin.cases r S.reference
  start := by simpa using (KrausChannel.identity u)
  before := Fin.cases B (fun j => S.before j)
  after := Fin.cases S.start (fun j => S.after j)
  finish := by simpa using S.finish

/-- Compiler from actual query/control syntax to the finite-memory array model. -/
def Circuit.toSkeleton : {n u v : ℕ} → Circuit a b n u v → Skeleton a b n u v
  | _, _, v, .control D =>
    { memory := fun _ => v
      reference := Fin.elim0
      start := D
      before := fun j => Fin.elim0 j
      after := fun j => Fin.elim0 j
      finish := KrausChannel.identity v }
  | _, _, _, .query B rest => rest.toSkeleton.prepend B

/-- Exact intermediate-state equality for the one-query compiler step. -/
theorem Skeleton.runAt_prepend (S : Skeleton a b n (r * b) v)
    (B : KrausChannel u (r * a)) (ρ : State u) (T : Effect v) (Φ : KrausChannel a b)
    (k : ℕ) (hk : k ≤ n) :
    ((S.prepend B).toProtocol ρ T).runAt Φ (k + 1) (Nat.succ_le_succ hk) =
      (S.toProtocol (outputState Φ r (B.onState ρ)) T).runAt Φ k hk := by
  induction k with
  | zero => simp [Protocol.runAt, Skeleton.toProtocol, Skeleton.prepend]
  | succ k ih =>
    let j : Fin n := ⟨k, Nat.lt_of_succ_le hk⟩
    have hh := ih (Nat.le_of_succ_le hk)
    have hmap := congrArg (fun X : State (S.memory j.castSucc) =>
      (S.after j).onState (outputState Φ (S.reference j) ((S.before j).onState X))) hh
    simpa only [Protocol.runAt, Skeleton.toProtocol, Skeleton.prepend, Fin.cases_succ] using hmap

/-- Every genuine finite circuit compiles to an actual adaptive protocol,
preserving its Born probability under every channel hypothesis. -/
theorem Circuit.compile_acceptance (C : Circuit a b n u v) (ρ : State u) (T : Effect v)
    (Φ : KrausChannel a b) :
    (C.toSkeleton.toProtocol ρ T).acceptance Φ = T.probability (C.run Φ ρ) := by
  induction C with
  | control D =>
    simp [Circuit.toSkeleton, Skeleton.toProtocol, Protocol.acceptance, Protocol.finalState,
      Protocol.runAt, KrausChannel.pullbackEffect_probability, Circuit.run]
  | @query k u v r B rest ih =>
    change (rest.toSkeleton.finish.pullbackEffect T).probability
      (((rest.toSkeleton.prepend B).toProtocol ρ T).runAt Φ (k + 1) (Nat.le_refl _)) = _
    rw [Skeleton.runAt_prepend]
    exact ih (outputState Φ _ (B.onState ρ)) T

end AdaptiveProtocol
end QuantumChannelStein
