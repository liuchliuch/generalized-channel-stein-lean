import GeneralizedChannelStein.UniformBounds
import GeneralizedChannelStein.DimensionDomination
import QuantumChannelStein.DominationTesting

/-! # Lemma 4, all three uniform bounds with the literal minimum eigenvalue -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DimensionDomination
open scoped ComplexOrder MatrixOrder
variable {a b : ℕ}

/-- The paper's faithful-replacer constant in bits. -/
def replacerRate (ω : State b) (hb : 0 < b) : ℝ :=
  Real.logb 2 (b:ℝ)-Real.logb 2 (minEigenvalue ω hb)

/-- Lemma 4, with all finite-block conclusions and no hidden domination premise.
The witnessing faithful state may be any witness of F3. -/
theorem lemma_4 (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    let C := replacerRate ω hb
    let E := familyEntropy (N.tensorPower n) (F n)
    let β := compositeBeta (N.tensorPower n) (F n) ε
    (0 ≤ E ∧ E ≤ ((n:ℝ)*C : EReal)) ∧
    (ENNReal.ofReal ((1-ε)*(2:ℝ)^(-(n:ℝ)*C)) ≤ β ∧ β ≤ ENNReal.ofReal (1-ε)) ∧
    (1-ε)*(-Real.logb 2 β.toReal) ≤ E.toReal+1 := by
  dsimp only
  let M := (ReplacerChannel.channel a ω).tensorPower n
  let c : ℝ := (2:ℝ)^((n:ℝ)*replacerRate ω hb)
  have hM : M.toLinearMap ∈ F n := replacer_power_mem F hF.tensor_closed ω hOne n hn
  have hdom : MatrixMap.CPLe (N.tensorPower n).toLinearMap ((c:ℂ) • M.toLinearMap) :=
    faithful_replacer_domination N ω hb hω n
  have hc : 1 ≤ c := one_le_domination_constant _ _ (N.tensorPower n).trace_apply M.trace_apply
    (PureReferenceRecovery.inputDensity (unitProductInput (pow_pos ha n))) hdom
  have hE := familyEntropy_upper_of_domination (N.tensorPower n) M (F n) hM c hc hdom
  have hcLog : Real.logb 2 c = (n:ℝ)*replacerRate ω hb := by
    dsimp [c]
    rw [Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)]
  rw [hcLog] at hE
  have hβ := compositeBeta_lower_of_domination (N.tensorPower n) M (F n) hM c
    (by linarith) hdom ε
  have hinv : (1-ε)/c = (1-ε)*(2:ℝ)^(-(n:ℝ)*replacerRate ω hb) := by
    dsimp [c]
    rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    congr 2
    ring
  rw [hinv] at hβ
  exact ⟨⟨familyEntropy_nonneg _ (pow_pos ha n) _,hE⟩,
    ⟨hβ,compositeBeta_le_one_sub _ (pow_pos ha n) _ ε hε.le hε1.le⟩,
    composite_weak_converse _ M (pow_pos ha n) (F n) hM c hc hdom ε hε.le hε1⟩

/-- The literal optimized quantities are finite, and beta is strictly positive,
from the basic family assumptions alone. -/
theorem admissible_values_finite (N : KrausChannel a b) (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    familyEntropy (N.tensorPower n) (F n) ≠ ⊤ ∧
    familyEntropy (N.tensorPower n) (F n) ≠ ⊥ ∧
    0 < compositeBeta (N.tensorPower n) (F n) ε ∧
    compositeBeta (N.tensorPower n) (F n) ε < ⊤ := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  obtain ⟨hE,hβ,_⟩ := lemma_4 N ha hb F hF ω hω hOne n hn ε hε hε1
  refine ⟨ne_of_lt (hE.2.trans_lt (EReal.coe_lt_top _)),
    ne_of_gt (EReal.bot_lt_zero.trans_le hE.1), ?_, hβ.2.trans_lt ENNReal.ofReal_lt_top⟩
  apply lt_of_lt_of_le _ hβ.1
  apply ENNReal.ofReal_pos.mpr
  exact mul_pos (sub_pos.mpr hε1) (Real.rpow_pos_of_pos (by norm_num) _)

end GeneralizedChannelStein
