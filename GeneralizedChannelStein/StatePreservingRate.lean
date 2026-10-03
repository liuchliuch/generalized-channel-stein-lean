import GeneralizedChannelStein.StatePreserving
import GeneralizedChannelStein.MainTheorems

/-! # The rate conclusion of Proposition 19, connected to the main theorem -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy RelativeEntropy Filter
open scoped Topology ComplexOrder
variable {a b : ℕ}

/-- The canonical generalized rate of a replacer is the genuine state Umegaki entropy. -/
theorem statePreserving_replacer_rate (τ : State a) (ρ ω : State b)
    (ha : 0 < a) (hb : 0 < b) (hω : ω.matrix.PosDef) :
    (steinRate (ReplacerChannel.channel a ρ) (statePreservingFamily τ ω):EReal) = umegaki ρ ω := by
  let N := ReplacerChannel.channel a ρ
  let F := statePreservingFamily τ ω
  have hF : Admissible F := statePreserving_admissible τ ω hω
  have h := entropy_limit N ha hb F hF
  have hconst : Tendsto (entropyRateReal N F) atTop (𝓝 (umegaki ρ ω).toReal) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    dsimp [entropyRateReal,N,F]
    rw [statePreserving_replacer_entropy τ ρ ω ha n,EReal.toReal_mul,EReal.toReal_coe]
    have hn0 : (n:ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
    field_simp
  have heq : steinRate N F = (umegaki ρ ω).toReal := tendsto_nhds_unique h hconst
  have hf := admissible_values_finite N ha hb F hF 1 (by norm_num) (1/2) (by norm_num) (by norm_num)
  have hOne : familyEntropy (N.tensorPower 1) (F 1) = umegaki ρ ω := by
    simpa only [Nat.cast_one,EReal.coe_one,one_mul] using statePreserving_replacer_entropy τ ρ ω ha 1
  rw [hOne] at hf
  rw [heq,EReal.coe_toReal hf.1 hf.2.1]

/-- **Proposition 19**, now including the common asymptotic rate identity. -/
theorem proposition_19_complete (τ : State a) (ω ρ : State b) (ha : 0 < a) (hb : 0 < b)
    (hτ : τ.matrix.PosDef) (hω : ω.matrix.PosDef) :
    Admissible (statePreservingFamily τ ω) ∧ QuantitativeAt (statePreservingFamily τ ω) τ ∧
    (∀ n, familyEntropy ((ReplacerChannel.channel a ρ).tensorPower n) (statePreservingFamily τ ω n) =
      ((n:ℝ):EReal)*umegaki ρ ω) ∧
    (∀ n ε, compositeBeta ((ReplacerChannel.channel a ρ).tensorPower n) (statePreservingFamily τ ω n) ε =
      stateBeta (PerfectDiscrimination.statePower ρ n) (PerfectDiscrimination.statePower ω n) ε) ∧
    (steinRate (ReplacerChannel.channel a ρ) (statePreservingFamily τ ω):EReal) = umegaki ρ ω := by
  obtain ⟨h1,h2,h3,h4⟩ := proposition_19 τ ω ρ ha hτ hω
  exact ⟨h1,h2,h3,h4,statePreserving_replacer_rate τ ρ ω ha hb hω⟩

end GeneralizedChannelStein
