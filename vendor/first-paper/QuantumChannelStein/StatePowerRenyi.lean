import QuantumChannelStein.PerfectDiscrimination
import QuantumChannelStein.SandwichedRenyiTensor
import QuantumChannelStein.InvariantSpectralBound

/-! # Actual state-power Rényi additivity and polynomial spectral multiplicity -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.StatePowerRenyi
open Matrix ChannelEntropy ChannelPowerReindex TensorPower PerfectDiscrimination
  RelativeEntropy SandwichedRenyi TensorPermutation
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

theorem statePower_zero_eq (ρ σ : State n) : statePower ρ 0 = statePower σ 0 := by
  apply state_eq_of_matrix_eq
  rfl

theorem statePower_succ (ρ : State n) (k : ℕ) :
    statePower ρ (k + 1) = (ρ.tensor (statePower ρ k)).reindex
      (finCongr (show n * n ^ k = n ^ (k + 1) by rw [Nat.pow_succ'])) := by
  apply state_eq_of_matrix_eq
  rfl

theorem supportIncluded_statePower (ρ σ : State n) (hs : supportIncluded ρ σ) (k : ℕ) :
    supportIncluded (statePower ρ k) (statePower σ k) := by
  induction k with
  | zero => rw [statePower_zero_eq ρ σ]
  | succ k ih =>
    rw [statePower_succ, statePower_succ, supportIncluded_reindex, supportIncluded_tensor_iff]
    exact ⟨hs, ih⟩

/-- Literal extended-real additivity for independently repeated density matrices. -/
theorem renyi_statePower (α : ℝ) (hα : 1 < α) (ρ σ : State n) (k : ℕ) :
    renyi α hα (statePower ρ k) (statePower σ k) = ((k : ℝ) : EReal) * renyi α hα ρ σ := by
  induction k with
  | zero =>
    rw [statePower_zero_eq ρ σ, renyi_self]
    simp
  | succ k ih =>
    rw [statePower_succ, statePower_succ, renyi_reindex, renyi_tensor, ih]
    rw [Nat.cast_add, Nat.cast_one, EReal.coe_add, EReal.coe_one,
      EReal.right_distrib_of_nonneg (by exact_mod_cast (Nat.cast_nonneg k : (0 : ℝ) ≤ k)) zero_le_one,
      one_mul, add_comm]

/-- The spectrum of a repeated state is unchanged by the exact finite-coordinate flattening. -/
theorem spectrum_statePower (σ : State n) (k : ℕ) :
    spectrum ℂ (statePower σ k).matrix = spectrum ℂ (TensorPower.tensorPower σ.matrix k) := by
  change spectrum ℂ ((Matrix.reindexAlgEquiv ℂ ℂ (channelIndexEquiv n k))
    (TensorPower.tensorPower σ.matrix k)) = _
  exact AlgEquiv.spectrum_eq _ _

/-- Genuine invariant-algebra counting yields a polynomial, not exponential, pinching multiplicity. -/
theorem spectrum_card_statePower_le (σ : State n) (k : ℕ) :
    (spectrum ℂ (statePower σ k).matrix).ncard ≤ (k + 1) ^ (n * n) := by
  rw [spectrum_statePower]
  have h := ncard_spectrum_invariant_le k
    (⟨TensorPower.tensorPower σ.matrix k, tensorPower_mem_invariantAlgebra σ.matrix k⟩ :
      invariantAlgebra (Fin n) k)
  simpa only [Fintype.card_fin] using h

end QuantumChannelStein.StatePowerRenyi
