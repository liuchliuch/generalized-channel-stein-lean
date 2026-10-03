import GeneralizedChannelStein.CompletionConsequences
import GeneralizedChannelStein.CompletionLossScalars

/-! # The literal normalized residual channel in the completion decomposition -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CompletionComponents
open QuantumChannelStein ChannelEntropy DiamondNorm
open scoped ComplexOrder
variable {a b : ℕ}

/-- Positive CP components of normalized channels have a normalized residual. -/
theorem exists_residual (L S : KrausChannel a b) (p : ℝ) (hp : p<1)
    (horder : MatrixMap.CPLe (Complex.ofReal p • L.toLinearMap) S.toLinearMap) :
    ∃ Q : KrausChannel a b, S.toLinearMap =
      Complex.ofReal p • L.toLinearMap + Complex.ofReal (1-p) • Q.toLinearMap := by
  let Q : MatrixMap a b := Complex.ofReal (1-p)⁻¹ •
    (S.toLinearMap-Complex.ofReal p • L.toLinearMap)
  have hcp : IsChannel Q := by
    constructor
    · exact MatrixMap.completelyPositive_smul (inv_pos.mpr (sub_pos.mpr hp)).le horder
    · intro X
      change ((Complex.ofReal (1-p)⁻¹) • (S.apply X-Complex.ofReal p • L.apply X)).trace = X.trace
      rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, S.trace_apply, L.trace_apply]
      simp only [smul_eq_mul]
      have hne : (1-(p:ℂ))≠0 := by exact_mod_cast (sub_pos.mpr hp).ne'
      push_cast
      field_simp
  obtain ⟨R,hR⟩ := (isChannel_iff_kraus Q).mp hcp
  refine ⟨R,?_⟩
  rw [hR]
  dsimp only [Q]
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (sub_pos.mpr hp).ne',
    Complex.ofReal_one,one_smul]
  module

/-- The paper's completion loss is nonnegative throughout its literal domain. -/
theorem loss_nonneg (K : ℝ) (hK : 0≤K) (n : ℕ) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1/16) :
    0≤completionLoss K n δ := by
  unfold completionLoss
  apply mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  apply Real.logb_nonneg (by norm_num)
  apply (le_div_iff₀ hδ).mpr
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  linarith

/-- The completed component has strictly positive weight strictly below one. -/
theorem component_weight_bounds (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (ε K : ℝ)
    (hε : 0<ε) (hε1 : ε<1) (hK : 0≤K)
    (n : ℕ) (hn : 0<n) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1/16) :
    0 < (compositeBeta (N.tensorPower n) (F n) ε).toReal*(2:ℝ)^(-completionLoss K n δ) ∧
    (compositeBeta (N.tensorPower n) (F n) ε).toReal*(2:ℝ)^(-completionLoss K n δ) < 1 := by
  have hf := admissible_values_finite N ha hb F hF n hn ε hε hε1
  have hp := ENNReal.toReal_pos hf.2.2.1.ne' hf.2.2.2.ne
  have hq := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-completionLoss K n δ)
  refine ⟨mul_pos hp hq,?_⟩
  have hq1 : (2:ℝ)^(-completionLoss K n δ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (loss_nonneg K hK n δ hδ hδ1))
  have hβ := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (compositeBeta_le_one_sub (N.tensorPower n) (pow_pos ha n) (F n) ε hε.le hε1.le)
  rw [ENNReal.toReal_ofReal (sub_pos.mpr hε1).le] at hβ
  have hh := mul_le_mul_of_nonneg_left hq1 hp.le
  nlinarith

/-- The actual free dominator splits into the accurate channel and a CPTP residual. -/
theorem completion_decomposition (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (ε K : ℝ)
    (hε : 0<ε) (hε1 : ε<1) (hcomp : CompletionProperty N F ε K)
    (n : ℕ) (hn : 0<n) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1/16) :
    let p := (compositeBeta (N.tensorPower n) (F n) ε).toReal*(2:ℝ)^(-completionLoss K n δ)
    0<p ∧ p<1 ∧ ∃ L S Q : KrausChannel (a^n) (b^n), S.toLinearMap∈F n ∧
      S.toLinearMap=Complex.ofReal p • L.toLinearMap+Complex.ofReal (1-p) • Q.toLinearMap ∧
      diamondNorm (L.toLinearMap-(N.tensorPower n).toLinearMap)≤ENNReal.ofReal δ := by
  dsimp only
  have hp := component_weight_bounds N ha hb F hF ε K hε hε1 hcomp.constant_nonneg n hn δ hδ hδ1
  obtain ⟨L,S,hS,horder,hclose⟩ := hcomp.complete n hn δ hδ hδ1
  obtain ⟨Q,hQ⟩ := exists_residual L S _ hp.2 horder
  exact ⟨hp.1,hp.2,L,S,Q,hS,hQ,hclose⟩

end GeneralizedChannelStein.CompletionComponents
