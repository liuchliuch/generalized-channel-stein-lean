import QuantumChannelStein.ChannelEntropy
import QuantumChannelStein.TensorDomination
import Mathlib.Data.EReal.Inv

/-!
# Elementary bounds for the channel regularization supremum

These results manipulate the exact tensor-power supremum from
`ChannelEntropy`. The domination assembly theorem takes the per-power
CP-domination statements explicitly; it does not assume a channel
entropy law or assert a limit interpretation of the supremum.
-/

noncomputable section
namespace QuantumChannelStein.ChannelEntropy

variable {n m : ℕ}

/-- Density matrices with the same underlying matrix are the same state. -/
theorem state_eq_of_matrix_eq {a : ℕ} (ρ σ : State a) (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- Pure channel outputs depend only on the represented linear map. -/
theorem pureOutput_congr {r : ℕ} (Φ Ψ : KrausChannel n m)
    (h : Φ.toLinearMap = Ψ.toLinearMap) (ψ : UnitPureInput r n) :
    pureOutput Φ ψ = pureOutput Ψ ψ := by
  apply state_eq_of_matrix_eq
  rw [pureOutput_matrix, pureOutput_matrix, ← MatrixMap.amplify_toLinearMap Φ,
    h, MatrixMap.amplify_toLinearMap]

/-- Channel divergence is independent of the choice of Kraus representation. -/
theorem channelD_congr (Φ Φ' Ψ Ψ' : KrausChannel n m)
    (hΦ : Φ.toLinearMap = Φ'.toLinearMap) (hΨ : Ψ.toLinearMap = Ψ'.toLinearMap) :
    channelD Φ Ψ = channelD Φ' Ψ' := by
  unfold channelD
  apply iSup_congr
  intro ψ
  rw [pureOutput_congr Φ Φ' hΦ ψ, pureOutput_congr Ψ Ψ' hΨ ψ]

/-- Merely transporting numerical dimension equalities changes no entropy. -/
theorem channelD_cast {n' m' : ℕ} (Φ Ψ : KrausChannel n m)
    (hn : n = n') (hm : m = m') :
    channelD (Φ.cast hn hm) (Ψ.cast hn hm) = channelD Φ Ψ := by
  cases hn
  cases hm
  rfl

/-- Every actual tensor-power rate is nonnegative in nonzero dimension. -/
theorem tensorPower_rate_nonneg (Φ Ψ : KrausChannel n m) (hn : 0 < n) (k : ℕ) :
    0 ≤ (((k : ℝ)⁻¹ : ℝ) : EReal) * channelD (Φ.tensorPower k) (Ψ.tensorPower k) := by
  apply EReal.mul_nonneg
  · exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  · exact channelD_nonneg _ _ (pow_pos hn k)

/-- The tensor-power supremum is nonnegative. -/
theorem regularizedD_nonneg (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    0 ≤ regularizedD Φ Ψ :=
  (tensorPower_rate_nonneg Φ Ψ hn 1).trans
    (tensorPower_rate_le_regularizedD Φ Ψ 1 (by decide))

/-- Self-divergence vanishes at every rate and hence under regularization. -/
theorem regularizedD_self (Φ : KrausChannel n m) (hn : 0 < n) :
    regularizedD Φ Φ = 0 := by
  apply le_antisymm _ (regularizedD_nonneg Φ Φ hn)
  apply iSup_le
  intro k
  apply iSup_le
  intro _
  rw [channelD_self _ (pow_pos hn k), mul_zero]

/-- A CP bound with constant `c^k` gives the uniform per-use logarithmic
bound after division by a positive block length. -/
theorem tensorPower_rate_le_log2_of_cpLe (Φ Ψ : KrausChannel n m)
    (c : ℝ) (hc : 1 ≤ c) (k : ℕ) (hk : 0 < k)
    (h : MatrixMap.CPLe (Φ.tensorPower k).toLinearMap
      (((c ^ k : ℝ) : ℂ) • (Ψ.tensorPower k).toLinearMap)) :
    (((k : ℝ)⁻¹ : ℝ) : EReal) * channelD (Φ.tensorPower k) (Ψ.tensorPower k) ≤
      (Real.logb 2 c : EReal) := by
  have hd := channelD_le_log2_of_cpLe (Φ.tensorPower k) (Ψ.tensorPower k)
    (c ^ k) (one_le_pow₀ hc) h
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hinv : (0 : EReal) ≤ (((k : ℝ)⁻¹ : ℝ) : EReal) := by
    exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  calc
    _ ≤ (((k : ℝ)⁻¹ : ℝ) : EReal) * (Real.logb 2 (c ^ k) : EReal) :=
      mul_le_mul_of_nonneg_left hd hinv
    _ = (Real.logb 2 c : EReal) := by
      rw [← EReal.coe_mul, Real.logb_pow, ← mul_assoc, inv_mul_cancel₀ hkR, one_mul]

/-- Explicit assembly: if the actual tensor powers satisfy CP domination
with constants `c^k`, then the exact regularization supremum is at most
`log₂ c`. This lemma does not supply or assume tensor CP closure itself. -/
theorem regularizedD_le_log2_of_tensorPower_cpLe (Φ Ψ : KrausChannel n m)
    (c : ℝ) (hc : 1 ≤ c)
    (h : ∀ k : ℕ, 0 < k → MatrixMap.CPLe (Φ.tensorPower k).toLinearMap
      (((c ^ k : ℝ) : ℂ) • (Ψ.tensorPower k).toLinearMap)) :
    regularizedD Φ Ψ ≤ (Real.logb 2 c : EReal) := by
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  exact tensorPower_rate_le_log2_of_cpLe Φ Ψ c hc k hk (h k hk)

/-- Original one-use CP domination suffices for the regularized bound:
the proved tensor CP theorem supplies all powers automatically. -/
theorem regularizedD_le_log2_of_cpLe (Φ Ψ : KrausChannel n m)
    (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    regularizedD Φ Ψ ≤ (Real.logb 2 c : EReal) := by
  apply regularizedD_le_log2_of_tensorPower_cpLe Φ Ψ c hc
  intro k _
  exact Φ.cpLe_tensorPower Ψ (le_trans zero_le_one hc) h k

/-- In particular, finite CP domination implies finite regularized
supremum divergence for the actual tensor-power channels. -/
theorem regularizedD_lt_top_of_cpLe (Φ Ψ : KrausChannel n m)
    (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    regularizedD Φ Ψ < ⊤ :=
  lt_of_le_of_lt (regularizedD_le_log2_of_cpLe Φ Ψ c hc h) (EReal.coe_lt_top _)

end QuantumChannelStein.ChannelEntropy
