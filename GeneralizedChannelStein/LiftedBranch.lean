import GeneralizedChannelStein.LiftedTesting
import GeneralizedChannelStein.LemmaFour

/-! Testing supplies an actual free lifted branch with a uniform overlap constant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix ChannelEntropy UniformApproximation BranchExtraction
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b e : ℕ}

def completionOverlap (ε : ℝ) : ℝ :=
  (1-Real.sqrt (1-ExtensionComparison.tolerance ε))/(1+Real.sqrt (1-ExtensionComparison.tolerance ε))

theorem completionOverlap_pos (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) : 0<completionOverlap ε := by
  obtain ⟨hδ,hδ1,ht⟩ := ExtensionComparison.parameters ε hε hε1
  unfold completionOverlap
  apply div_pos
  · have hs : Real.sqrt (1-ExtensionComparison.tolerance ε)<1 :=
      (Real.sqrt_lt (by linarith) (by norm_num)).mpr (by linarith)
    linarith
  · positivity

theorem lifted_testing_branch (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap∈F 1) (he : 0<e)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : Vᴴ*V=1) (hVN : dilationMap V=N.toLinearMap)
    (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ∃ (p : ℝ) (M : KrausChannel (a^n) ((b*e)^n))
      (Z : Matrix (Fin ((b*e)^n)) (Fin (a^n)) ℂ),
      0<p ∧ p≤1 ∧ M.toLinearMap∈liftedFamily F e n ∧ ‖Z‖≤1 ∧
      (BranchExtraction.realPart ((powerIsometry (AuxiliaryExtensions.outputIsometry V) n)ᴴ*Z)-
        completionOverlap ε • (1:Operator (a^n))).PosSemidef ∧
      MatrixMap.CPLe ((p:ℂ) • adMap Z) M.toLinearMap ∧
      ExtensionComparison.factor ε*(compositeBeta (N.tensorPower n) (F n) ε).toReal≤p := by
  let G := liftedFamily F e
  have hG : Admissible G := liftedFamily_admissible F hF ω hω hOne he
  let δ := ExtensionComparison.tolerance ε
  obtain ⟨hδ,hδ1,ht⟩ := ExtensionComparison.parameters ε hε hε1
  let T := liftedTarget V hV n
  let γ := compositeBeta T (G n) δ
  have hγle : γ≤1 := (compositeBeta_le_one_sub T (pow_pos ha n) (G n) δ hδ.le hδ1.le).trans
    (by apply ENNReal.ofReal_le_one.mpr; linarith)
  have hγtop : γ≠⊤ := ne_of_lt (hγle.trans_lt (by simp))
  have hlow := lifted_beta_lower N ha F hF V hV hVN n hn ε hε hε1
  have hlowreal : ExtensionComparison.factor ε*(compositeBeta (N.tensorPower n) (F n) ε).toReal≤γ.toReal := by
    have h := ENNReal.toReal_mono hγtop hlow
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal ht.le] using h
  have hf := admissible_values_finite N ha hb F hF n hn ε hε hε1
  have hβp : 0<(compositeBeta (N.tensorPower n) (F n) ε).toReal :=
    ENNReal.toReal_pos hf.2.2.1.ne' hf.2.2.2.ne
  have hγp : 0<γ.toReal := (mul_pos ht hβp).trans_le hlowreal
  obtain ⟨M,hM,hβ⟩ := lemma_5_hardest T (pow_pos ha n) (G n) (hG.channels n hn)
    (hG.compact n hn) (hG.convex n hn) (hG.nonempty n hn) δ hδ.le
  have hs : 0<singleBeta (BranchExtraction.isometryChannel
      (powerIsometry (AuxiliaryExtensions.outputIsometry V) n)
      (powerIsometry_isometry _ (AuxiliaryExtensions.outputIsometry_isometry V hV) n)) M δ := by
    change 0<singleBeta T M δ
    rw [←hβ]
    exact (ENNReal.toReal_pos_iff.mp hγp).1
  obtain ⟨Z,hZn,hZo,hZcp⟩ := BranchExtraction.lemma_25
    (powerIsometry (AuxiliaryExtensions.outputIsometry V) n)
    (powerIsometry_isometry _ (AuxiliaryExtensions.outputIsometry_isometry V hV) n)
    M (pow_pos ha n) δ hδ hδ1 hs
  refine ⟨γ.toReal,M,Z,hγp,?_,hM,hZn,hZo,?_,hlowreal⟩
  · exact (ENNReal.toReal_mono (by simp) hγle).trans_eq (by simp)
  · change MatrixMap.CPLe (((singleBeta T M δ).toReal:ℂ) • adMap Z) M.toLinearMap at hZcp
    rw [←hβ] at hZcp
    exact hZcp

end GeneralizedChannelStein
