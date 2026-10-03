import QuantumChannelStein.ChannelRenyi
import QuantumChannelStein.OperationalTesting

/-!
# Actual finite-memory adaptive protocol semantics

The same initial density matrix and the same finite CPTP controls are used
under both hypotheses. Memory and reference dimensions may vary at every
use. The recurrence below is generic in the explicit chain property. Its concrete
proof is in RenyiChannelChainAllOrders; FinalSteinTheorems exports Theorem 2.1.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.AdaptiveProtocol
open SandwichedRenyi OperationalTesting
variable {a b n : ℕ}

/-- A finite adaptive strategy with arbitrary finite working memories and
references. Preparation and postprocessing are actual normalized Kraus maps. -/
structure Protocol (a b n : ℕ) where
  memory : Fin (n + 1) → ℕ
  reference : Fin n → ℕ
  initial : State (memory 0)
  before : (j : Fin n) → KrausChannel (memory j.castSucc) (reference j * a)
  after : (j : Fin n) → KrausChannel (reference j * b) (memory j.succ)
  effect : Effect (memory (Fin.last n))

/-- Actual state after k uses under the selected channel hypothesis. -/
def Protocol.runAt (P : Protocol a b n) (Φ : KrausChannel a b) :
    (k : ℕ) → (hk : k ≤ n) → State (P.memory ⟨k, Nat.lt_succ_of_le hk⟩)
  | 0, _ => P.initial
  | k + 1, hk =>
    let j : Fin n := ⟨k, Nat.lt_of_succ_le hk⟩
    (P.after j).onState (outputState Φ (P.reference j)
      ((P.before j).onState (P.runAt Φ k (Nat.le_of_succ_le hk))))

/-- The actual terminal density matrix after the prescribed number of uses. -/
def Protocol.finalState (P : Protocol a b n) (Φ : KrausChannel a b) :
    State (P.memory (Fin.last n)) := P.runAt Φ n le_rfl

/-- Final actual Born acceptance of the strategy under one channel hypothesis. -/
def Protocol.acceptance (P : Protocol a b n) (Φ : KrausChannel a b) : ℝ :=
  P.effect.probability (P.finalState Φ)

theorem Protocol.acceptance_nonneg (P : Protocol a b n) (Φ : KrausChannel a b) :
    0 ≤ P.acceptance Φ := P.effect.probability_nonneg _

theorem Protocol.acceptance_le_one (P : Protocol a b n) (Φ : KrausChannel a b) :
    P.acceptance Φ ≤ 1 := P.effect.probability_le_one _

/-- The explicit one-shot channel chain inequality (3.9), on genuine mixed
reference-assisted inputs. This property is proved in RenyiChannelChainAllOrders. -/
def HasRenyiChannelChain (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel a b) : Prop :=
  ∀ r : ℕ, ∀ ρ σ : State (r * a),
    renyi α hα (outputState Φ r ρ) (outputState Ψ r σ) ≤
      renyi α hα ρ σ + ChannelRenyi.regularizedD α hα Φ Ψ

/-- The actual adaptive recurrence, using only the explicitly labelled
one-shot chain premise and the already proved state Rényi DPI. -/
theorem Protocol.runAt_renyi_le (P : Protocol a b n) (Φ Ψ : KrausChannel a b)
    (α : ℝ) (hα : 1 < α) (hchain : HasRenyiChannelChain α hα Φ Ψ)
    (d : ℝ) (hd : ChannelRenyi.regularizedD α hα Φ Ψ ≤ (d : EReal))
    (k : ℕ) (hk : k ≤ n) :
    renyi α hα (P.runAt Φ k hk) (P.runAt Ψ k hk) ≤ (((k : ℝ) * d : ℝ) : EReal) := by
  induction k with
  | zero => simp [Protocol.runAt]
  | succ k ih =>
    let j : Fin n := ⟨k, Nat.lt_of_succ_le hk⟩
    let ρ := P.runAt Φ k (Nat.le_of_succ_le hk)
    let σ := P.runAt Ψ k (Nat.le_of_succ_le hk)
    have hbefore := renyi_data_processing α hα (P.before j) ρ σ
    have huse := hchain (P.reference j) ((P.before j).onState ρ) ((P.before j).onState σ)
    have hafter := renyi_data_processing α hα (P.after j)
      (outputState Φ (P.reference j) ((P.before j).onState ρ))
      (outputState Ψ (P.reference j) ((P.before j).onState σ))
    have hprev : renyi α hα ρ σ ≤ (((k : ℝ) * d : ℝ) : EReal) := ih (Nat.le_of_succ_le hk)
    change renyi α hα ((P.after j).onState _) ((P.after j).onState _) ≤ _
    calc
      _ ≤ _ := hafter
      _ ≤ _ := huse
      _ ≤ (((k : ℝ) * d : ℝ) : EReal) + (d : EReal) := add_le_add (hbefore.trans hprev) hd
      _ = _ := by rw [← EReal.coe_add]; congr 1; push_cast; ring

/-- The final-state divergence is at most n times the actual regularized
Rényi rate, whenever the one-shot chain inequality is available. -/
theorem Protocol.finalState_renyi_le (P : Protocol a b n) (Φ Ψ : KrausChannel a b)
    (α : ℝ) (hα : 1 < α) (hchain : HasRenyiChannelChain α hα Φ Ψ)
    (d : ℝ) (hd : ChannelRenyi.regularizedD α hα Φ Ψ ≤ (d : EReal)) :
    renyi α hα (P.finalState Φ) (P.finalState Ψ) ≤ (((n : ℝ) * d : ℝ) : EReal) :=
  P.runAt_renyi_le Φ Ψ α hα hchain d hd n le_rfl

end QuantumChannelStein.AdaptiveProtocol
