import GeneralizedChannelStein.BranchExtraction

/-! # Genuine acceptance-amplitude bound for an approximate CP branch

The single-Kraus branch is factored into the prescribed Stinespring environment
by the checked exact auxiliary theorem. Both acceptance probabilities refer
to actual normalized channel outputs, uniformly over the tester.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.ExtensionAmplitude
open QuantumChannelStein Matrix ChannelEntropy OperationalTesting TestingPrimal
  HockeyStickApproximation BranchExtraction UniformAuxiliary ParallelTestingReduction
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- The actual one-use amplitude inequality, at any nonnegative CP budget,
including t=0, for every fixed-reference pure input and every effect. -/
theorem pure_sqrt_acceptance_le (J Z : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (M : KrausChannel a b) (t s : ℝ) (ht : 0 ≤ t)
    (hdom : MatrixMap.CPLe (adMap Z) ((t:ℂ) • M.toLinearMap))
    (herr : ‖J-Z‖ ≤ s) (ψ : UnitPureInput a a) (T : Effect (a*b)) :
    Real.sqrt (T.probability (pureOutput (isometryChannel J hJ) ψ)) ≤
      Real.sqrt t * Real.sqrt (T.probability (pureOutput M ψ)) + s := by
  obtain ⟨C,hC,hfactor⟩ := lemma_6_exact (lift Z) M.stinespring t ht (by
    simpa only [dilationMap_lift, ParallelConverse.dilationMap_stinespring] using hdom)
  have heq : lift Z = ((1 : Operator b) ⊗ₖ C)*M.stinespring := sub_eq_zero.mp hfactor
  have he : ‖lift J-((1 : Operator b) ⊗ₖ C)*M.stinespring‖ ≤ s := by
    rw [← heq, show lift J-lift Z=lift (J-Z) from rfl, norm_lift]
    exact herr
  have h := Purification.lemma_3_4 (isometryChannel J hJ) M (lift J) M.stinespring
    (traceEnvironment_of_dilationMap _ _ (dilationMap_isometry_lift J hJ))
    (traceEnvironment_of_dilationMap _ _ (ParallelConverse.dilationMap_stinespring M))
    C (pureMatrix ψ.val) (pureMatrix_positive ψ.val)
    (trace_pureMatrix_of_norm_one ψ.val ψ.property) (rawEffect T)
    (rawEffect_positive T) (rawEffect_complement_positive T)
  rw [← pureOutput_probability_raw, ← pureOutput_probability_raw] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _)) he)

/-- The same inequality for every mixed input and every finite reference.
One probability-preserving normal-form test works for both hypotheses. -/
theorem sqrt_acceptance_le (J Z : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (M : KrausChannel a b) (t s : ℝ) (ht : 0 ≤ t)
    (hdom : MatrixMap.CPLe (adMap Z) ((t:ℂ) • M.toLinearMap))
    (herr : ‖J-Z‖ ≤ s) (P : ChannelTest a b) :
    Real.sqrt (P.acceptance (isometryChannel J hJ)) ≤
      Real.sqrt t * Real.sqrt (P.acceptance M) + s := by
  obtain ⟨ψ,T,hP⟩ := exists_pure_test P
  have h := pure_sqrt_acceptance_le J Z hJ M t s ht hdom herr ψ T
  rwa [hP,hP] at h

/-- The exact scalar constants for the extension comparison. The stronger
coefficient β/epsilon is retained before the final harmless weakening. -/
theorem scalar_acceptance_lower (ε β p q : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hβ : 0 < β) (hq : 0 ≤ q)
    (hp : ((1+Real.sqrt (1-ε))/2)^2 ≤ p)
    (hamp : Real.sqrt p ≤ Real.sqrt (ε/β)*Real.sqrt q+Real.sqrt (1-ε)) :
    (β/ε) * (1-Real.sqrt (1-ε))^2/4 ≤ q ∧
      β * (1-Real.sqrt (1-ε))^2/4 ≤ q := by
  let s := Real.sqrt (1-ε)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2=1-ε := Real.sq_sqrt (by linarith)
  have hs1 : s < 1 := by nlinarith
  have hp0 : 0 ≤ p := (sq_nonneg _).trans hp
  have hroot : (1+s)/2 ≤ Real.sqrt p := by
    have hsq := Real.sq_sqrt hp0
    have hr := Real.sqrt_nonneg p
    dsimp only [s] at hp ⊢
    nlinarith
  have hgap : (1-s)/2 ≤ Real.sqrt (ε/β)*Real.sqrt q := by
    change Real.sqrt p ≤ Real.sqrt (ε/β)*Real.sqrt q+s at hamp
    linarith
  have ht : 0 ≤ ε/β := div_nonneg hε.le hβ.le
  have hproduct : (Real.sqrt (ε/β)*Real.sqrt q)^2=(ε/β)*q := by
    rw [mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hq]
  have hsq : ((1-s)/2)^2 ≤ (ε/β)*q := by
    rw [← hproduct]
    exact pow_le_pow_left₀ (by linarith) hgap 2
  have hstrong : (β/ε)*(1-s)^2/4 ≤ q := by
    have hh := mul_le_mul_of_nonneg_left hsq (div_nonneg hβ.le hε.le)
    have hcancel : (β/ε)*((ε/β)*q)=q := by field_simp
    rw [hcancel] at hh
    nlinarith
  refine ⟨hstrong, ?_⟩
  apply le_trans _ hstrong
  have hcoeff : β ≤ β/ε := (le_div_iff₀ hε).mpr (by nlinarith)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)) (by norm_num)

/-- The exact dimension-independent lower testing constant used in Lemma 26,
for actual mixed/reference-assisted acceptance probabilities. -/
theorem acceptance_lower (J Z : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (M : KrausChannel a b) (ε β : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hβ : 0 < β)
    (hdom : MatrixMap.CPLe (adMap Z) (Complex.ofReal (ε/β) • M.toLinearMap))
    (herr : ‖J-Z‖ ≤ Real.sqrt (1-ε)) (P : ChannelTest a b)
    (hp : ((1+Real.sqrt (1-ε))/2)^2 ≤ P.acceptance (isometryChannel J hJ)) :
    (β/ε) * (1-Real.sqrt (1-ε))^2/4 ≤ P.acceptance M ∧
      β * (1-Real.sqrt (1-ε))^2/4 ≤ P.acceptance M := by
  apply scalar_acceptance_lower ε β _ _ hε hε1 hβ (P.acceptance_nonneg M) hp
  exact sqrt_acceptance_le J Z hJ M (ε/β) (Real.sqrt (1-ε))
    (div_nonneg hε.le hβ.le) hdom herr P

/-- The pure-input specialization with the exact constants, matching the
literal compositePureBeta test class. -/
theorem pure_acceptance_lower (J Z : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1)
    (M : KrausChannel a b) (ε β : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hβ : 0 < β)
    (hdom : MatrixMap.CPLe (adMap Z) (Complex.ofReal (ε/β) • M.toLinearMap))
    (herr : ‖J-Z‖ ≤ Real.sqrt (1-ε))
    (ψ : UnitPureInput a a) (T : Effect (a*b))
    (hp : ((1+Real.sqrt (1-ε))/2)^2 ≤ T.probability (pureOutput (isometryChannel J hJ) ψ)) :
    (β/ε) * (1-Real.sqrt (1-ε))^2/4 ≤ T.probability (pureOutput M ψ) ∧
      β * (1-Real.sqrt (1-ε))^2/4 ≤ T.probability (pureOutput M ψ) := by
  simpa only [ofPureTest_acceptance] using acceptance_lower J Z hJ M ε β hε hε1 hβ
    hdom herr (ofPureTest ψ T) (by simpa only [ofPureTest_acceptance] using hp)

end GeneralizedChannelStein.ExtensionAmplitude
