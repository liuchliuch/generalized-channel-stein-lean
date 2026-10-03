import QuantumChannelStein.TensorMap

/-! # CP domination through actual repeated independent channel uses -/
noncomputable section
namespace QuantumChannelStein
open scoped ComplexOrder
namespace KrausChannel
variable {n m : ℕ}

/-- Transport of a CP comparison through dimension equalities. -/
theorem cpLe_cast {n' m' : ℕ} (Φ Ψ : KrausChannel n m)
    (hn : n = n') (hm : m = m') (c : ℝ)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    MatrixMap.CPLe (Φ.cast hn hm).toLinearMap ((c : ℂ) • (Ψ.cast hn hm).toLinearMap) := by
  cases hn
  cases hm
  exact h

/-- CP domination tensorizes with the exact scalar power, as required by Lemma 3.1. -/
theorem cpLe_tensorPower (Φ Ψ : KrausChannel n m) {c : ℝ} (hc : 0 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) (k : ℕ) :
    MatrixMap.CPLe (tensorPower Φ k).toLinearMap
      (((c ^ k : ℝ) : ℂ) • (tensorPower Ψ k).toLinearMap) := by
  induction k with
  | zero =>
    simpa [tensorPower] using MatrixMap.cpLe_refl (identity 1).toLinearMap
  | succ k ih =>
    have htensor := MatrixMap.cpLe_tensor (MatrixMap.completelyPositive_toLinearMap Φ)
      (MatrixMap.completelyPositive_smul (pow_nonneg hc k)
        (MatrixMap.completelyPositive_toLinearMap (tensorPower Ψ k))) h ih
    have hraw : MatrixMap.CPLe (tensor Φ (tensorPower Φ k)).toLinearMap
        (((c ^ (k + 1) : ℝ) : ℂ) • (tensor Ψ (tensorPower Ψ k)).toLinearMap) := by
      simpa only [MatrixMap.tensor_smul_left, MatrixMap.tensor_smul_right,
        smul_smul, MatrixMap.tensor_kraus_toLinearMap, ← Complex.ofReal_mul,
        ← pow_succ'] using htensor
    exact cpLe_cast (tensor Φ (tensorPower Φ k)) (tensor Ψ (tensorPower Ψ k)) _ _ _ hraw

end KrausChannel
end QuantumChannelStein
