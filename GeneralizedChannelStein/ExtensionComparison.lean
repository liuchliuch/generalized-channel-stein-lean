import GeneralizedChannelStein.AuxiliaryExtensions
import GeneralizedChannelStein.ExtensionAmplitude

/-! # Lemma 26: exact dimension-independent auxiliary-output comparison -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.ExtensionComparison
open QuantumChannelStein Matrix ChannelEntropy OperationalTesting
  BranchExtraction AuxiliaryExtensions
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b e : ℕ}

def tolerance (ε : ℝ) : ℝ := 1-((1+Real.sqrt (1-ε))/2)^2
def factor (ε : ℝ) : ℝ := (1-Real.sqrt (1-ε))^2/4

theorem parameters (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    0<tolerance ε ∧ tolerance ε<1 ∧ 0<factor ε := by
  have hs : 0≤Real.sqrt (1-ε) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (1-ε))^2=1-ε := Real.sq_sqrt (by linarith)
  have hs1 : Real.sqrt (1-ε)<1 := by nlinarith
  dsimp [tolerance,factor]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · exact div_pos (sq_pos_of_pos (by linarith)) (by norm_num)

/-- The hardest original alternative has one actual CPTP extension whose
single branch enforces the comparison uniformly over every lifted tester. -/
theorem lower_comparison (N : KrausChannel a b) (ha : 0<a)
    (F : Set (MatrixMap a b)) (hF : ∀ M ∈ F, IsChannel M)
    (hc : IsCompact (MatrixMap.choi '' F)) (hv : Convex ℝ (MatrixMap.choi '' F)) (hne : F.Nonempty)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) (hVN : dilationMap V=N.toLinearMap)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ENNReal.ofReal (factor ε)*compositeBeta N F ε ≤
      compositeBeta (isometryChannel (outputIsometry V) (outputIsometry_isometry V hV))
        (extensionFamily F) (tolerance ε) := by
  by_cases hz : compositeBeta N F ε=0
  · simp [hz]
  have htop : compositeBeta N F ε≠⊤ :=
    ne_of_lt ((compositeBeta_le_one_sub N ha F ε hε.le hε1.le).trans_lt ENNReal.ofReal_lt_top)
  let β := (compositeBeta N F ε).toReal
  have hβ : 0<β := ENNReal.toReal_pos hz htop
  obtain ⟨M,hM,hMβ⟩ := lemma_5_hardest N ha F hF hc hv hne ε hε.le
  have hβM : ENNReal.ofReal β≤singleBeta N M ε := by
    rw [ENNReal.ofReal_toReal htop,← hMβ]
  obtain ⟨L,Z,hred,hdom,herr⟩ := extension_with_close_branch N M ha V hV hVN ε β hε hε1 hβ hβM
  have hL : L.toLinearMap ∈ extensionFamily F := by
    apply (extension_mem_iff F L).mpr
    rwa [hred]
  have hfactor : 0≤factor ε := (parameters ε hε hε1).2.2.le
  calc
    _ = ENNReal.ofReal (factor ε*β) := by
      rw [ENNReal.ofReal_mul hfactor,ENNReal.ofReal_toReal htop]
    _ ≤ compositeBeta (isometryChannel (outputIsometry V) (outputIsometry_isometry V hV))
        (extensionFamily F) (tolerance ε) := by
      apply le_iInf
      intro T
      have hp : ((1+Real.sqrt (1-ε))/2)^2≤T.val.acceptance
          (isometryChannel (outputIsometry V) (outputIsometry_isometry V hV)) := by
        have ht := T.property
        dsimp [tolerance] at ht
        linarith
      have hq := (ExtensionAmplitude.acceptance_lower (outputIsometry V) Z
        (outputIsometry_isometry V hV) L ε β hε hε1 hβ hdom herr T.val hp).2
      apply (ENNReal.ofReal_le_ofReal ?_).trans (acceptance_le_worst (extensionFamily F) T.val L hL)
      dsimp [factor]
      nlinarith

/-- Lemma 26, both literal inequalities and exactly the stated parameter domain. -/
theorem lemma_26 (N : KrausChannel a b) (ha : 0<a)
    (F : Set (MatrixMap a b)) (hF : ∀ M ∈ F, IsChannel M)
    (hc : IsCompact (MatrixMap.choi '' F)) (hv : Convex ℝ (MatrixMap.choi '' F)) (hne : F.Nonempty)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) (hVN : dilationMap V=N.toLinearMap)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    0<tolerance ε ∧ tolerance ε<1 ∧ 0<factor ε ∧
    ENNReal.ofReal (factor ε)*compositeBeta N F ε ≤
      compositeBeta (isometryChannel (outputIsometry V) (outputIsometry_isometry V hV))
        (extensionFamily F) (tolerance ε) ∧
    compositeBeta (isometryChannel (outputIsometry V) (outputIsometry_isometry V hV))
      (extensionFamily F) ε ≤ compositeBeta N F ε := by
  obtain ⟨hδ,hδ1,ht⟩ := parameters ε hε hε1
  refine ⟨hδ,hδ1,ht,lower_comparison N ha F hF hc hv hne V hV hVN ε hε hε1,?_⟩
  exact extensionBeta_le_original N _ ((reduced_isometry_map V hV).trans hVN) F ε

end GeneralizedChannelStein.ExtensionComparison
