import QuantumChannelStein.SandwichedRenyiBasics
import QuantumChannelStein.ChannelEntropyFiniteness

/-! # Actual reference-assisted channel sandwiched Rényi divergence

The optimization is over the same normalized pure inputs as channel
Umegaki entropy. The regularization is the supremum of positive-block
rates of the actual Kraus tensor powers. Limit identification is proved
separately from genuine tensor additivity.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ChannelRenyi
open ChannelEntropy SandwichedRenyi
variable {n m r : ℕ}

def channelD (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m) : EReal :=
  ⨆ ψ : UnitPureInput n n, renyi α hα (pureOutput Φ ψ) (pureOutput Ψ ψ)

def regularizedD (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m) : EReal :=
  ⨆ k : ℕ, ⨆ (_ : 0 < k),
    (((k : ℝ)⁻¹ : ℝ) : EReal) * channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k)

theorem renyi_pureOutput_le_channelD (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m)
    (ψ : UnitPureInput n n) :
    renyi α hα (pureOutput Φ ψ) (pureOutput Ψ ψ) ≤ channelD α hα Φ Ψ :=
  le_iSup (fun φ : UnitPureInput n n => renyi α hα (pureOutput Φ φ) (pureOutput Ψ φ)) ψ

theorem pureOutput_renyi_le (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap))
    (ψ : UnitPureInput r n) :
    renyi α hα (pureOutput Φ ψ) (pureOutput Ψ ψ) ≤ (Real.logb 2 c : EReal) :=
  renyi_le_log2_of_domination α hα hα2 _ _ c hc (pureOutput_domination Φ Ψ c h ψ)

theorem channelD_le_log2_of_cpLe (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    channelD α hα Φ Ψ ≤ (Real.logb 2 c : EReal) := by
  apply iSup_le
  intro ψ
  exact pureOutput_renyi_le α hα hα2 Φ Ψ c hc h ψ

theorem channelD_lt_top_of_cpLe (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    channelD α hα Φ Ψ < ⊤ :=
  lt_of_le_of_lt (channelD_le_log2_of_cpLe α hα hα2 Φ Ψ c hc h) (EReal.coe_lt_top _)

theorem channelD_nonneg (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    0 ≤ channelD α hα Φ Ψ :=
  (renyi_nonneg α hα (pureOutput Φ (unitProductInput hn))
    (pureOutput Ψ (unitProductInput hn))).trans
      (renyi_pureOutput_le_channelD α hα Φ Ψ (unitProductInput hn))

theorem channelD_self (α : ℝ) (hα : 1 < α) (Φ : KrausChannel n m) (hn : 0 < n) :
    channelD α hα Φ Φ = 0 := by
  apply le_antisymm _ (channelD_nonneg α hα Φ Φ hn)
  apply iSup_le
  intro ψ
  simp

theorem channelD_congr (α : ℝ) (hα : 1 < α) (Φ Φ' Ψ Ψ' : KrausChannel n m)
    (hΦ : Φ.toLinearMap = Φ'.toLinearMap) (hΨ : Ψ.toLinearMap = Ψ'.toLinearMap) :
    channelD α hα Φ Ψ = channelD α hα Φ' Ψ' := by
  unfold channelD
  apply iSup_congr
  intro ψ
  rw [pureOutput_congr Φ Φ' hΦ ψ, pureOutput_congr Ψ Ψ' hΨ ψ]

theorem channelD_cast (α : ℝ) (hα : 1 < α) {n' m' : ℕ} (Φ Ψ : KrausChannel n m)
    (hn : n = n') (hm : m = m') :
    channelD α hα (Φ.cast hn hm) (Ψ.cast hn hm) = channelD α hα Φ Ψ := by
  cases hn
  cases hm
  rfl

theorem tensorPower_rate_le_regularizedD (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m)
    (k : ℕ) (hk : 0 < k) :
    (((k : ℝ)⁻¹ : ℝ) : EReal) * channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k) ≤
      regularizedD α hα Φ Ψ :=
  le_iSup_of_le k (le_iSup_of_le hk le_rfl)

theorem regularizedD_nonneg (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m) (hn : 0 < n) :
    0 ≤ regularizedD α hα Φ Ψ := by
  have h := tensorPower_rate_le_regularizedD α hα Φ Ψ 1 (by decide)
  simp only [Nat.cast_one, inv_one, EReal.coe_one, one_mul] at h
  exact (channelD_nonneg α hα _ _ (pow_pos hn 1)).trans h

theorem tensorPower_rate_le_log2_of_cpLe (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (c : ℝ) (hc : 1 ≤ c) (k : ℕ) (hk : 0 < k)
    (h : MatrixMap.CPLe (Φ.tensorPower k).toLinearMap
      (((c ^ k : ℝ) : ℂ) • (Ψ.tensorPower k).toLinearMap)) :
    (((k : ℝ)⁻¹ : ℝ) : EReal) * channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k) ≤
      (Real.logb 2 c : EReal) := by
  have hd := channelD_le_log2_of_cpLe α hα hα2 (Φ.tensorPower k) (Ψ.tensorPower k)
    (c ^ k) (one_le_pow₀ hc) h
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hinv : (0 : EReal) ≤ (((k : ℝ)⁻¹ : ℝ) : EReal) := by
    exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  calc
    _ ≤ (((k : ℝ)⁻¹ : ℝ) : EReal) * (Real.logb 2 (c ^ k) : EReal) :=
      mul_le_mul_of_nonneg_left hd hinv
    _ = (Real.logb 2 c : EReal) := by
      rw [← EReal.coe_mul, Real.logb_pow, ← mul_assoc, inv_mul_cancel₀ hkR, one_mul]

theorem regularizedD_le_log2_of_cpLe (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    regularizedD α hα Φ Ψ ≤ (Real.logb 2 c : EReal) := by
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  exact tensorPower_rate_le_log2_of_cpLe α hα hα2 Φ Ψ c hc k hk
    (Φ.cpLe_tensorPower Ψ (zero_le_one.trans hc) h k)

theorem regularizedD_lt_top_of_cpLe (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    regularizedD α hα Φ Ψ < ⊤ :=
  lt_of_le_of_lt (regularizedD_le_log2_of_cpLe α hα hα2 Φ Ψ c hc h) (EReal.coe_lt_top _)

theorem regularizedD_lt_top_of_umegaki_finite (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (hn : 0 < n) (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤) :
    regularizedD α hα Φ Ψ < ⊤ := by
  obtain ⟨c, hc, hcp⟩ := (ChannelEntropy.regularizedD_lt_top_iff_exists_cpLe Φ Ψ hn).mp hfinite
  exact regularizedD_lt_top_of_cpLe α hα hα2 Φ Ψ c hc hcp

theorem channelD_tensorPower_one (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m) :
    channelD α hα (Φ.tensorPower 1) (Ψ.tensorPower 1) = channelD α hα Φ Ψ := by
  rw [← channelD_cast α hα (Φ.tensorPower 1) (Ψ.tensorPower 1) (Nat.pow_one n) (Nat.pow_one m)]
  exact channelD_congr α hα _ Φ _ Ψ Φ.tensorPower_one_toLinearMap Ψ.tensorPower_one_toLinearMap

theorem channelD_le_regularizedD (α : ℝ) (hα : 1 < α) (Φ Ψ : KrausChannel n m) :
    channelD α hα Φ Ψ ≤ regularizedD α hα Φ Ψ := by
  have h := tensorPower_rate_le_regularizedD α hα Φ Ψ 1 (by decide)
  simpa only [Nat.cast_one, inv_one, EReal.coe_one, one_mul, channelD_tensorPower_one] using h

end QuantumChannelStein.ChannelRenyi
