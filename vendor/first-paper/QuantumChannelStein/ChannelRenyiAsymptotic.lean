import QuantumChannelStein.ChannelRenyiLimit
import QuantumChannelStein.RenyiExponentialScalars

/-! # Passing uniform block estimates to the genuine regularized Rényi limit -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ChannelRenyi
open ChannelEntropy SandwichedRenyi Filter
open scoped Topology
variable {n m : ℕ}

/-- An eventual linear bound has the claimed slope at the proved Fekete limit. -/
theorem regularizedD_le_of_eventually_linear_bound (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (hn : 0 < n) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) (M B : ℝ)
    (hbound : ∀ᶠ k : ℕ in atTop,
      channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k) ≤ ((k : ℝ) * M + B : ℝ)) :
    regularizedD α hα Φ Ψ ≤ (M : EReal) := by
  have htop := (regularizedD_lt_top_of_cpLe α hα hα2 Φ Ψ c hc h).ne
  have hbot : regularizedD α hα Φ Ψ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (regularizedD_nonneg α hα Φ Ψ hn))
  have hlim := tendsto_real_rate_of_cpLe α hα hα2 Φ Ψ hn c hc h
  have hupper : Tendsto (fun k : ℕ => M + B / (k : ℝ)) atTop (𝓝 M) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat B)
  have hreal : (regularizedD α hα Φ Ψ).toReal ≤ M := by
    apply le_of_tendsto_of_tendsto hlim hupper
    filter_upwards [hbound, eventually_gt_atTop 0] with k hk hk0
    have hakTop := (channelD_lt_top_of_cpLe α hα hα2 (Φ.tensorPower k) (Ψ.tensorPower k)
      (c ^ k) (one_le_pow₀ hc) (Φ.cpLe_tensorPower Ψ (zero_le_one.trans hc) h k)).ne
    have hakBot : channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k) ≠ ⊥ :=
      ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (channelD_nonneg α hα _ _ (pow_pos hn k)))
    have hr : (channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k)).toReal ≤ (k : ℝ) * M + B := by
      apply EReal.coe_le_coe_iff.mp
      rwa [EReal.coe_toReal hakTop hakBot]
    calc
      _ ≤ ((k : ℝ) * M + B) / (k : ℝ) := div_le_div_of_nonneg_right hr (Nat.cast_nonneg k)
      _ = _ := by field_simp
  rw [← EReal.coe_toReal htop hbot]
  exact EReal.coe_le_coe_iff.mpr hreal

/-- Uniform actual-state quasi-root estimates imply the regularized channel bound. -/
theorem regularizedD_le_of_eventually_quasi_root_bound (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (hn : 0 < n) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) (M C : ℝ) (hC : 0 < C)
    (hbound : ∀ᶠ k : ℕ in atTop, ∀ ψ : UnitPureInput (n ^ k) (n ^ k),
      quasi α (pureOutput (Φ.tensorPower k) ψ).matrix (pureOutput (Ψ.tensorPower k) ψ).matrix ^
        (1 / (2 * α)) ≤ C * (2 : ℝ) ^ ((k : ℝ) * ((α - 1) / (2 * α)) * M)) :
    regularizedD α hα Φ Ψ ≤ (M : EReal) := by
  apply regularizedD_le_of_eventually_linear_bound α hα hα2 Φ Ψ hn c hc h M
    ((2 * α / (α - 1)) * Real.logb 2 C)
  filter_upwards [hbound] with k hk
  apply iSup_le
  intro ψ
  have hdom := pureOutput_domination (Φ.tensorPower k) (Ψ.tensorPower k) (c ^ k)
    (Φ.cpLe_tensorPower Ψ (zero_le_one.trans hc) h k) ψ
  have hs := SupportDomination.ker_le_of_posSemidef_smul_sub (pureOutput (Φ.tensorPower k) ψ).positive hdom
  exact renyi_le_of_quasi_root_exponential α hα _ _ hs C M k hC (hk ψ)

end QuantumChannelStein.ChannelRenyi
