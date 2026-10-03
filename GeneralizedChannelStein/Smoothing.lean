import GeneralizedChannelStein.ApproximationTesting

/-! # Literal free-family max-relative entropy with exact CPTP smoothing

The inner domination cost includes lam≥1; its infimum is taken in ENNReal,
so an absent dominator gives infinity. The logarithm is the genuine extended
logarithm. No `toReal` is applied before finiteness is proved. The smoothing
variable is a normalized Kraus channel, not a trace-nonincreasing map.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DiamondNorm
variable {a b : ℕ}

/-- Inner scalar domination infimum from equation (resource-max). -/
def dominationCost (L S : KrausChannel a b) : ENNReal :=
  ⨅ lam : {lam : ℝ // 1 ≤ lam ∧ MatrixMap.CPLe L.toLinearMap ((lam:ℂ) • S.toLinearMap)},
    ENNReal.ofReal lam.val

/-- Base-two extended logarithm. -/
def log2Cost (x : ENNReal) : EReal := ((Real.log 2)⁻¹ : ℝ) * x.log

/-- Free optimization AFTER the individual domination infimum and logarithm. -/
def resourceMax (L : KrausChannel a b) (F : Set (MatrixMap a b)) : EReal :=
  ⨅ S : FreeChannel F, log2Cost (dominationCost L S.val)

/-- Exact trace-preserving smoothing, in the unhalved diamond norm. -/
def smoothedResourceMax (N : KrausChannel a b) (F : Set (MatrixMap a b)) (δ : ℝ) : EReal :=
  ⨅ L : {L : KrausChannel a b //
    diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ}, resourceMax L.val F

theorem one_le_dominationCost (L S : KrausChannel a b) : 1 ≤ dominationCost L S := by
  apply le_iInf
  intro lam
  exact_mod_cast ENNReal.ofReal_le_ofReal lam.property.1

theorem log2Cost_nonneg {x : ENNReal} (hx : 1 ≤ x) : 0 ≤ log2Cost x := by
  apply mul_nonneg
  · exact_mod_cast inv_nonneg.mpr (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  · simpa only [ENNReal.log_one] using ENNReal.log_monotone hx

theorem resourceMax_nonneg (L : KrausChannel a b) (F : Set (MatrixMap a b)) :
    0 ≤ resourceMax L F := by
  apply le_iInf
  intro S
  exact log2Cost_nonneg (one_le_dominationCost L S.val)

theorem smoothedResourceMax_nonneg (N : KrausChannel a b)
    (F : Set (MatrixMap a b)) (δ : ℝ) : 0 ≤ smoothedResourceMax N F δ := by
  apply le_iInf
  intro L
  exact resourceMax_nonneg L.val F

/-- A concrete finite domination cost proves a concrete max-relative-entropy bound. -/
theorem resourceMax_le_of_domination (L S : KrausChannel a b)
    (F : Set (MatrixMap a b)) (hS : S.toLinearMap ∈ F)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hdom : MatrixMap.CPLe L.toLinearMap ((lam:ℂ) • S.toLinearMap)) :
    resourceMax L F ≤ (Real.logb 2 lam : EReal) := by
  have hp : 0 < lam := by linarith
  have hc : dominationCost L S ≤ ENNReal.ofReal lam := iInf_le_of_le ⟨lam,hlam,hdom⟩ le_rfl
  have hl : (dominationCost L S).log ≤ (Real.log lam : EReal) := by
    calc
      _ ≤ (ENNReal.ofReal lam).log := ENNReal.log_monotone hc
      _ = _ := by rw [ENNReal.log_ofReal,if_neg (not_le.mpr hp)]
  refine (iInf_le_of_le ⟨S,hS⟩ le_rfl).trans ?_
  calc
    log2Cost (dominationCost L S) ≤
        (((Real.log 2)⁻¹ : ℝ) : EReal) * (Real.log lam : EReal) :=
      mul_le_mul_of_nonneg_left hl (EReal.coe_nonneg.mpr
        (inv_nonneg.mpr (Real.log_pos (by norm_num : (1:ℝ)<2)).le))
    _ = (Real.logb 2 lam : EReal) := by
      rw [← EReal.coe_mul]
      congr 1
      rw [Real.logb,div_eq_mul_inv,mul_comm]

/-- This upper bound requires an actual CPTP witness close to the target. -/
theorem smoothedResourceMax_le_of_witness (N L S : KrausChannel a b)
    (F : Set (MatrixMap a b)) (hS : S.toLinearMap ∈ F)
    (lam δ : ℝ) (hlam : 1 ≤ lam)
    (hdom : MatrixMap.CPLe L.toLinearMap ((lam:ℂ) • S.toLinearMap))
    (hclose : diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ) :
    smoothedResourceMax N F δ ≤ (Real.logb 2 lam : EReal) := by
  calc
    _ ≤ resourceMax L F := iInf_le_of_le ⟨L,hclose⟩ le_rfl
    _ ≤ _ := resourceMax_le_of_domination L S F hS lam hlam hdom

theorem log2Cost_mono : Monotone log2Cost := by
  intro x y hxy
  exact mul_le_mul_of_nonneg_left (ENNReal.log_monotone hxy)
    (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Real.log_pos (by norm_num : (1:ℝ)<2)).le))

theorem log2Cost_ofReal (x : ℝ) (hx : 0 < x) :
    log2Cost (ENNReal.ofReal x) = (Real.logb 2 x : EReal) := by
  unfold log2Cost
  rw [ENNReal.log_ofReal,if_neg (not_le.mpr hx), ← EReal.coe_mul]
  congr 1
  rw [Real.logb,div_eq_mul_inv,mul_comm]

/-- Equation (AEP-lower), before asymptotic passage, with exact TP and full diamond radius. -/
theorem smoothedResourceMax_testing_lower (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (ε δ : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hδ : 0 ≤ δ) (hmargin : 0 < 1-ε-δ/2)
    (hβ : 0 < compositeBeta N F ε) :
    ((-Real.logb 2 (compositeBeta N F ε).toReal+Real.logb 2 (1-ε-δ/2) : ℝ) : EReal) ≤
      smoothedResourceMax N F δ := by
  have hbnd := compositeBeta_le_one_sub N ha F ε hε hε1.le
  have htop : compositeBeta N F ε ≠ ⊤ := ne_of_lt (hbnd.trans_lt ENNReal.ofReal_lt_top)
  have hB : 0 < (compositeBeta N F ε).toReal := ENNReal.toReal_pos hβ.ne' htop
  apply le_iInf
  intro L
  apply le_iInf
  intro S
  have hc : ENNReal.ofReal ((1-ε-δ/2)/(compositeBeta N F ε).toReal) ≤
      dominationCost L.val S.val := by
    apply le_iInf
    intro lam
    apply ENNReal.ofReal_le_ofReal
    have hlam : 0 < lam.val := by linarith [lam.property.1]
    have htest := compositeBeta_lower_of_approximation N L.val S.val F S.property
      lam.val δ hlam hδ lam.property.2 L.property ε
    have ht := (ENNReal.ofReal_le_iff_le_toReal htop).mp htest
    apply (div_le_iff₀ hB).mpr
    have hh := (div_le_iff₀ hlam).mp ht
    nlinarith
  have hlog := log2Cost_mono hc
  rw [log2Cost_ofReal _ (div_pos hmargin hB),Real.logb_div hmargin.ne' hB.ne'] at hlog
  convert hlog using 1 <;> congr 1 <;> ring

end GeneralizedChannelStein
