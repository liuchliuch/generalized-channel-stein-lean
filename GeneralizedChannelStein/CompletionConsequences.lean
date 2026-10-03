import GeneralizedChannelStein.CompletionStatement
import GeneralizedChannelStein.CommonDominator

/-! # Finite smoothing and testing consequences of concrete completion witnesses -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CompletionConsequences
open QuantumChannelStein ChannelEntropy DiamondNorm
open scoped ComplexOrder
variable {a b : ℕ}

/-- Invert a strictly positive actual component weight in CP order. -/
theorem cpLe_of_component (L S : KrausChannel a b) (w : ℝ) (hw : 0<w)
    (h : MatrixMap.CPLe (Complex.ofReal w • L.toLinearMap) S.toLinearMap) :
    MatrixMap.CPLe L.toLinearMap (Complex.ofReal w⁻¹ • S.toLinearMap) := by
  have hh := cpLe_real_scale h w⁻¹ (inv_pos.mpr hw).le
  simpa only [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hw.ne',
    Complex.ofReal_one, one_smul] using hh

/-- Concrete witnesses give the exact advertised finite smoothing upper bound. -/
theorem smoothing_upper (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (ε K : ℝ)
    (hε : 0<ε) (hε1 : ε<1) (hcomp : CompletionProperty N F ε K)
    (n : ℕ) (hn : 0<n) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1/16) :
    smoothedResourceMax (N.tensorPower n) (F n) δ ≤
      ((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
        completionLoss K n δ : ℝ) : EReal) := by
  obtain ⟨L,S,hS,horder,hclose⟩ := hcomp.complete n hn δ hδ hδ1
  have hfin := admissible_values_finite N ha hb F hF n hn ε hε hε1
  have hβ : 0 < (compositeBeta (N.tensorPower n) (F n) ε).toReal :=
    ENNReal.toReal_pos hfin.2.2.1.ne' hfin.2.2.2.ne
  let w := (compositeBeta (N.tensorPower n) (F n) ε).toReal * (2:ℝ)^(-completionLoss K n δ)
  have hw : 0<w := mul_pos hβ (Real.rpow_pos_of_pos (by norm_num) _)
  have hdom := cpLe_of_component L S w hw horder
  have hcost : 1 ≤ w⁻¹ := one_le_domination_constant _ _ L.trace_apply S.trace_apply
    (PureReferenceRecovery.inputDensity (unitProductInput (pow_pos ha n))) hdom
  have hh := smoothedResourceMax_le_of_witness (N.tensorPower n) L S (F n) hS
    w⁻¹ δ hcost hdom hclose
  have heq : Real.logb 2 w⁻¹ = -Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
      completionLoss K n δ := by
    rw [Real.logb_inv]
    dsimp [w]
    rw [Real.logb_mul hβ.ne' (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne',
      Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)]
    ring
  rwa [heq] at hh

/-- The lower smoothing bound needs only the basic family axioms and any valid full radius. -/
theorem smoothing_lower (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (ε : ℝ)
    (hε : 0<ε) (hε1 : ε<1) (n : ℕ) (hn : 0<n)
    (δ : ℝ) (hδ : 0≤δ) (hmargin : 0<1-ε-δ/2) :
    ((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
      Real.logb 2 (1-ε-δ/2) : ℝ) : EReal) ≤
      smoothedResourceMax (N.tensorPower n) (F n) δ :=
  smoothedResourceMax_testing_lower _ (pow_pos ha n) _ ε δ hε.le hε1 hδ hmargin
    (admissible_values_finite N ha hb F hF n hn ε hε hε1).2.2.1

/-- Conditional finite-block corollary; the numbered unconditional endpoint will use Theorem 16. -/
theorem smoothing_bounds (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (ε K : ℝ)
    (hε : 0<ε) (hε1 : ε<1) (hcomp : CompletionProperty N F ε K)
    (n : ℕ) (hn : 0<n) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1/16)
    (hmargin : ε+δ/2<1) :
    (((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
      Real.logb 2 (1-ε-δ/2) : ℝ) : EReal) ≤ smoothedResourceMax (N.tensorPower n) (F n) δ) ∧
    (smoothedResourceMax (N.tensorPower n) (F n) δ ≤
      ((-Real.logb 2 (compositeBeta (N.tensorPower n) (F n) ε).toReal +
        completionLoss K n δ : ℝ) : EReal)) :=
  ⟨smoothing_lower N ha hb F hF ε hε hε1 n hn δ hδ.le (by linarith),
    smoothing_upper N ha hb F hF ε K hε hε1 hcomp n hn δ hδ hδ1⟩

end GeneralizedChannelStein.CompletionConsequences
