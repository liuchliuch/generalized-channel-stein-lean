import GeneralizedChannelStein.AEPLower

/-! # Theorem 11: exact-CPTP smoothed resource asymptotic equipartition -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DiamondNorm DimensionDomination Filter Asymptotics
open scoped Topology ComplexOrder
variable {a b : ℕ}

theorem zero_diamondNorm (a b : ℕ) : diamondNorm (0 : MatrixMap a b) = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  change ENNReal.ofReal (TraceNorm.traceNorm (0 : Matrix (Fin r × Fin b) (Fin r × Fin b) ℂ)) ≤ 0
  simp [TraceNorm.traceNorm_zero]

/-- Finiteness is established from an actual exact target and a faithful free dominator. -/
theorem smoothedResourceMax_finite (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) (n : ℕ) (hn : 0 < n) (δ : ℝ) :
    smoothedResourceMax (N.tensorPower n) (F n) δ ≠ ⊤ ∧
    smoothedResourceMax (N.tensorPower n) (F n) δ ≠ ⊥ := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  let M := (ReplacerChannel.channel a ω).tensorPower n
  have hM : M.toLinearMap ∈ F n := replacer_power_mem F hF.tensor_closed ω hOne n hn
  have hC := replacerRate_nonneg ω hb hω
  have hc : 1 ≤ (2:ℝ)^((n:ℝ)*replacerRate ω hb) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg n) hC)
  have hclose : diamondNorm ((N.tensorPower n).toLinearMap-(N.tensorPower n).toLinearMap) ≤
      ENNReal.ofReal δ := by rw [sub_self,zero_diamondNorm]; exact zero_le _
  have h := smoothedResourceMax_le_of_witness (N.tensorPower n) (N.tensorPower n) M (F n) hM
    ((2:ℝ)^((n:ℝ)*replacerRate ω hb)) δ hc (faithful_replacer_domination N ω hb hω n) hclose
  exact ⟨ne_of_lt (h.trans_lt (EReal.coe_lt_top _)),
    ne_of_gt (EReal.bot_lt_zero.trans_le (smoothedResourceMax_nonneg _ _ _))⟩

/-- **Theorem 11**, the literal finite real normalized cost. The radius
hypotheses are required only at positive blocklengths; no F0 constraint is added. -/
theorem theorem_11 (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F) (δ : ℕ → ℝ) (δbar : ℝ)
    (hδ : ∀ n, 0 < n → 0 < δ n ∧ δ n ≤ δbar) (hbar : δbar < 2)
    (hsub : (fun n => Real.logb 2 (1/δ n)) =o[atTop] (fun n : ℕ => (n:ℝ))) :
    Tendsto (fun n : ℕ => (smoothedResourceMax (N.tensorPower n) (F n) (δ n)).toReal/(n:ℝ))
      atTop (𝓝 (steinRate N F)) := by
  have h := (EReal.tendsto_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).comp
    (theorem_11_extended N ha hb F hF δ δbar hδ hbar hsub)
  simp only [EReal.toReal_coe] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hf := smoothedResourceMax_finite N ha hb F hF n hn (δ n)
  change (smoothedRate N F δ n).toReal = _
  rw [smoothedRate,EReal.toReal_mul,EReal.toReal_coe]
  ring

end GeneralizedChannelStein
