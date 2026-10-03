import QuantumChannelStein.Kraus
import QuantumChannelStein.QuantumOperatorBridge

/-! Transport of the actual finite Kraus channel to Lean-Quantum's CPTP type. -/
noncomputable section
namespace QuantumChannelStein.MatrixOperatorBridge
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n m : ℕ}

attribute [local instance] operatorCStar operatorStar operatorStarRing
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def channelMap (Φ : KrausChannel n m) :
    QuantumChannel.T (H n) (H m) :=
  ∑ i, QuantumChannel.krausTerm (Φ.kraus i).toEuclideanLin

@[simp] theorem channelMap_op (Φ : KrausChannel n m) (A : M n) :
    channelMap Φ (opEquiv n A) = opEquiv m (Φ.apply A) := by
  simp only [channelMap, LinearMap.sum_apply, QuantumChannel.krausTerm,
    KrausChannel.apply, map_sum, opEquiv_apply, toEuclideanLin_mul,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.comp_assoc]
  rfl

theorem channelMap_isCompletelyPositive (Φ : KrausChannel n m) :
    QuantumChannel.IsCompletelyPositive (channelMap Φ) :=
  QuantumChannel.sum_krausTerm_isCompletelyPositive
    (fun i : Fin Φ.rank => (Φ.kraus i).toEuclideanLin)

def channelCP (Φ : KrausChannel n m) :
    CompletelyPositiveMap (QuantumState.L (H n)) (QuantumState.L (H m)) :=
  Classical.choose (channelMap_isCompletelyPositive Φ)

theorem channelCP_toLinearMap (Φ : KrausChannel n m) :
    (channelCP Φ).toLinearMap = channelMap Φ :=
  Classical.choose_spec (channelMap_isCompletelyPositive Φ)

def channelCPTP (Φ : KrausChannel n m) : QuantumChannel.CPTP (H n) (H m) where
  toCompletelyPositiveMap := channelCP Φ
  trace_map X := by
    change QuantumState.Tr X = QuantumState.Tr ((channelCP Φ).toLinearMap X)
    rw [channelCP_toLinearMap]
    obtain ⟨A, rfl⟩ := (opEquiv n).surjective X
    change QuantumState.Tr (opEquiv n A) =
      QuantumState.Tr (channelMap Φ (opEquiv n A))
    rw [channelMap_op]
    change LinearMap.trace ℂ (H n) (opEquiv n A) =
      LinearMap.trace ℂ (H m) (opEquiv m (Φ.apply A))
    rw [trace_op, trace_op, Φ.trace_apply]

@[simp] theorem channelCPTP_op (Φ : KrausChannel n m) (A : M n) :
    (channelCPTP Φ).toFun (opEquiv n A) = opEquiv m (Φ.apply A) := by
  change (channelCP Φ).toLinearMap (opEquiv n A) = _
  rw [channelCP_toLinearMap, channelMap_op]

end QuantumChannelStein.MatrixOperatorBridge
