import QuantumChannelStein.ChannelRenyiTensor
import Mathlib.Analysis.Subadditive
import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Fekete identification of the actual regularized sandwiched Rényi rate -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ChannelRenyi
open Filter
open scoped Topology
variable {n m : ℕ}

theorem tendsto_rate_of_cpLe (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2) (Φ Ψ : KrausChannel n m) (hn : 0 < n)
    (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    Tendsto (fun k : ℕ => (((k : ℝ)⁻¹ : ℝ) : EReal) *
      channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k)) atTop (𝓝 (regularizedD α hα Φ Ψ)) := by
  let a : ℕ → EReal := fun k => channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k)
  have hanonneg (k : ℕ) : 0 ≤ a k := channelD_nonneg α hα _ _ (pow_pos hn k)
  have hatop (k : ℕ) : a k ≠ ⊤ :=
    (channelD_lt_top_of_cpLe α hα hα2 (Φ.tensorPower k) (Ψ.tensorPower k) (c ^ k)
      (one_le_pow₀ hc) (Φ.cpLe_tensorPower Ψ (le_trans zero_le_one hc) h k)).ne
  have habot (k : ℕ) : a k ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hanonneg k))
  have hacoe (k : ℕ) : ((a k).toReal : EReal) = a k := EReal.coe_toReal (hatop k) (habot k)
  have habound (k : ℕ) : (a k).toReal ≤ (k : ℝ) * Real.logb 2 c := by
    apply EReal.coe_le_coe_iff.mp
    rw [hacoe]
    simpa only [Real.logb_pow] using
      channelD_le_log2_of_cpLe α hα hα2 (Φ.tensorPower k) (Ψ.tensorPower k) (c ^ k)
        (one_le_pow₀ hc) (Φ.cpLe_tensorPower Ψ (le_trans zero_le_one hc) h k)
  let u : ℕ → ℝ := fun k => -(a k).toReal
  have hsub : Subadditive u := by
    intro k l
    have hr : (a k).toReal + (a l).toReal ≤ (a (k + l)).toReal := by
      apply EReal.coe_le_coe_iff.mp
      rw [EReal.coe_add, hacoe, hacoe, hacoe]
      exact channelD_tensorPower_superadditive α hα Φ Ψ k l
    dsimp [u]
    linarith
  have hbdd : BddBelow (Set.range fun k : ℕ => u k / (k : ℝ)) := by
    refine ⟨-Real.logb 2 c, ?_⟩
    rintro _ ⟨k, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [Nat.cast_zero, div_zero]
      exact neg_nonpos.mpr (Real.logb_nonneg (by norm_num) hc)
    · apply (le_div_iff₀ (Nat.cast_pos.mpr hk : (0 : ℝ) < k)).mpr
      dsimp [u]
      nlinarith [habound k]
  have hreal : Tendsto (fun k : ℕ => (a k).toReal / (k : ℝ)) atTop (𝓝 (-hsub.lim)) := by
    simpa only [u, neg_div, neg_neg] using (hsub.tendsto_lim hbdd).neg
  have hcoe := EReal.tendsto_coe.mpr hreal
  have hrate (k : ℕ) : (((a k).toReal / (k : ℝ) : ℝ) : EReal) =
      (((k : ℝ)⁻¹ : ℝ) : EReal) * a k := by
    rw [div_eq_mul_inv, EReal.coe_mul, hacoe, mul_comm]
  have hlimit : Tendsto (fun k : ℕ => (((k : ℝ)⁻¹ : ℝ) : EReal) * a k)
      atTop (𝓝 ((-hsub.lim : ℝ) : EReal)) :=
    hcoe.congr' (Eventually.of_forall hrate)
  have hupper : regularizedD α hα Φ Ψ ≤ ((-hsub.lim : ℝ) : EReal) := by
    apply iSup_le
    intro k
    apply iSup_le
    intro hk
    change (((k : ℝ)⁻¹ : ℝ) : EReal) * a k ≤ _
    rw [← hrate]
    apply EReal.coe_le_coe
    have hh := hsub.lim_le_div hbdd (Nat.ne_of_gt hk)
    dsimp [u] at hh
    rw [neg_div] at hh
    linarith
  have hlower : ((-hsub.lim : ℝ) : EReal) ≤ regularizedD α hα Φ Ψ := by
    apply le_of_tendsto hlimit
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact tensorPower_rate_le_regularizedD α hα Φ Ψ k hk
  have heq : ((-hsub.lim : ℝ) : EReal) = regularizedD α hα Φ Ψ := le_antisymm hlower hupper
  rwa [heq] at hlimit


/-- Every finite Umegaki channel rate has the claimed genuine Rényi rate limit. -/
theorem tendsto_rate_of_umegaki_finite (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (hn : 0 < n) (hfinite : ChannelEntropy.regularizedD Φ Ψ < ⊤) :
    Tendsto (fun k : ℕ => (((k : ℝ)⁻¹ : ℝ) : EReal) *
      channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k)) atTop (𝓝 (regularizedD α hα Φ Ψ)) := by
  obtain ⟨c, hc, hcp⟩ := (ChannelEntropy.regularizedD_lt_top_iff_exists_cpLe Φ Ψ hn).mp hfinite
  exact tendsto_rate_of_cpLe α hα hα2 Φ Ψ hn c hc hcp

/-- Real-valued version used in the quantitative right-continuity proof. -/
theorem tendsto_real_rate_of_cpLe (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (Φ Ψ : KrausChannel n m) (hn : 0 < n) (c : ℝ) (hc : 1 ≤ c)
    (h : MatrixMap.CPLe Φ.toLinearMap ((c : ℂ) • Ψ.toLinearMap)) :
    Tendsto (fun k : ℕ => (channelD α hα (Φ.tensorPower k) (Ψ.tensorPower k)).toReal / (k : ℝ))
      atTop (𝓝 (regularizedD α hα Φ Ψ).toReal) := by
  have htop : regularizedD α hα Φ Ψ ≠ ⊤ := (regularizedD_lt_top_of_cpLe α hα hα2 Φ Ψ c hc h).ne
  have hbot : regularizedD α hα Φ Ψ ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (regularizedD_nonneg α hα Φ Ψ hn))
  have hh := (EReal.tendsto_toReal htop hbot).comp (tendsto_rate_of_cpLe α hα hα2 Φ Ψ hn c hc h)
  simpa only [Function.comp_def, EReal.toReal_mul, EReal.toReal_coe,
    div_eq_mul_inv, mul_comm] using hh

end QuantumChannelStein.ChannelRenyi
