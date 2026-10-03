import GeneralizedChannelStein.IsometricBenchmarks

/-! Exact CPTP smoothing of isometries. The sharp distance bound uses the
positive residual of pinching domination rather than a roots-of-unity expansion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TestingSDP ChannelEntropy DiamondNorm TraceNorm TraceDefectCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

theorem trace_amplify_of_scaling (Q : MatrixMap a b) (c : ℂ)
    (ht : ∀ X, (Q X).trace=c*X.trace) (r : ℕ) (X : BipartiteOperator r a) :
    (MatrixMap.amplify Q r X).trace=c*X.trace := by
  change (∑ i : Fin r × Fin b, Q (fun u v => X (i.1,u) (i.1,v)) i.2 i.2) = _
  rw [Fintype.sum_prod_type]
  have he (i : Fin r) : (∑ j : Fin b, Q (fun u v => X (i,u) (i,v)) j j) =
      c*∑ u : Fin a, X (i,u) (i,u) := ht _
  simp only [he,Matrix.trace,Matrix.diag,Fintype.sum_prod_type,Finset.mul_sum]

theorem diamondNorm_le_of_cp_trace_scaling (Q : MatrixMap a b) (hQ : MatrixMap.CompletelyPositive Q)
    (c : ℝ) (hc : 0≤c) (ht : ∀ X, (Q X).trace=(c:ℂ)*X.trace) :
    diamondNorm Q ≤ ENNReal.ofReal c := by
  rw [diamondNorm_eq_pureDiamondNorm Q (cp_hermiticityPreserving Q hQ)]
  apply iSup_le
  intro ψ
  apply ENNReal.ofReal_le_ofReal
  rw [traceNorm_of_posSemidef _ (hQ a _ (pureMatrix_positive ψ.val)),
    trace_amplify_of_scaling Q c ht,trace_pureMatrix_of_norm_one ψ.val ψ.property,mul_one,Complex.ofReal_re]

theorem diamondNorm_smul_le (Q : MatrixMap a b) (s d : ℝ) (hs : 0≤s) (hd : 0≤d)
    (hQ : diamondNorm Q ≤ ENNReal.ofReal d) :
    diamondNorm ((s:ℂ) • Q) ≤ ENNReal.ofReal (s*d) := by
  apply iSup_le; intro r
  apply iSup_le; intro X
  have hb : ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify Q r X.val)) ≤ diamondNorm Q :=
    le_iSup_of_le r (le_iSup_of_le X le_rfl)
  have hreal := (ENNReal.ofReal_le_ofReal_iff hd).mp (hb.trans hQ)
  have he : MatrixMap.amplify ((s:ℂ) • Q) r X.val = (s:ℂ) • MatrixMap.amplify Q r X.val := rfl
  rw [he,TraceNorm.traceNorm_smul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hreal hs)

/-- A normalized CP domination N≤cM yields the sharp generic distance bound. -/
theorem diamond_distance_of_domination (N M : KrausChannel a b) (c : ℝ) (hc : 1≤c)
    (hdom : MatrixMap.CPLe N.toLinearMap ((c:ℂ) • M.toLinearMap)) :
    diamondNorm (M.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal (2*(1-c⁻¹)) := by
  have hcpos : 0<c := by linarith
  have hcinv : 0≤c⁻¹ := inv_nonneg.mpr hcpos.le
  have hc1 : 0≤1-c⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hc)
  let Q : MatrixMap a b := M.toLinearMap-(c⁻¹:ℂ) • N.toLinearMap
  have hQ : MatrixMap.CompletelyPositive Q := by
    have h := MatrixMap.completelyPositive_smul hcinv hdom
    have he : (c⁻¹:ℂ) • ((c:ℂ) • M.toLinearMap-N.toLinearMap)=Q := by
      dsimp [Q]
      rw [smul_sub,smul_smul]
      have hec : (c⁻¹:ℂ)*(c:ℂ)=1 := by norm_cast; exact inv_mul_cancel₀ hcpos.ne'
      rw [hec,one_smul]
    simp only [Complex.ofReal_inv] at h
    rw [he] at h
    exact h
  have hQt : ∀ X, (Q X).trace=((1-c⁻¹:ℝ):ℂ)*X.trace := by
    intro X
    change (M.apply X-(c⁻¹:ℂ) • N.apply X).trace=_
    rw [Matrix.trace_sub,Matrix.trace_smul,KrausChannel.trace_apply,KrausChannel.trace_apply]
    simp [Complex.ofReal_sub,smul_eq_mul]
    ring
  have hQnorm := diamondNorm_le_of_cp_trace_scaling Q hQ (1-c⁻¹) hc1 hQt
  have hPnorm := diamondNorm_le_of_cp_trace_scaling (((1-c⁻¹:ℝ):ℂ) • N.toLinearMap)
    (MatrixMap.completelyPositive_smul hc1 (MatrixMap.completelyPositive_toLinearMap N)) (1-c⁻¹) hc1 (by
      intro X
      change (((1-c⁻¹:ℝ):ℂ) • N.apply X).trace=_
      rw [Matrix.trace_smul,KrausChannel.trace_apply]; rfl)
  have he : M.toLinearMap-N.toLinearMap = Q + -(((1-c⁻¹:ℝ):ℂ) • N.toLinearMap) := by
    dsimp [Q]
    simp only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_inv]
    module
  rw [he]
  calc
    _ ≤ diamondNorm Q+diamondNorm (-(((1-c⁻¹:ℝ):ℂ) • N.toLinearMap)) := diamondNorm_add_le _ _
    _ = diamondNorm Q+diamondNorm (((1-c⁻¹:ℝ):ℂ) • N.toLinearMap) := by rw [diamondNorm_neg]
    _ ≤ ENNReal.ofReal (1-c⁻¹)+ENNReal.ofReal (1-c⁻¹) := add_le_add hQnorm hPnorm
    _ = ENNReal.ofReal (2*(1-c⁻¹)) := by rw [← ENNReal.ofReal_add hc1 hc1]; congr 1; ring

/-- An actual CPTP convex mixture, with its map equation retained. -/
theorem exists_channel_mixture (N M : KrausChannel a b) (s : ℝ) (hs : 0≤s) (hs1 : s≤1) :
    ∃ L : KrausChannel a b, L.toLinearMap=((1-s:ℝ):ℂ) • N.toLinearMap+(s:ℂ) • M.toLinearMap := by
  apply (isChannel_iff_kraus _).mp
  constructor
  · exact MatrixMap.completelyPositive_add
      (MatrixMap.completelyPositive_smul (sub_nonneg.mpr hs1) (MatrixMap.completelyPositive_toLinearMap N))
      (MatrixMap.completelyPositive_smul hs (MatrixMap.completelyPositive_toLinearMap M))
  · intro X
    change (((1-s:ℝ):ℂ) • N.apply X+(s:ℂ) • M.apply X).trace=X.trace
    rw [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_smul,KrausChannel.trace_apply,KrausChannel.trace_apply,
      ← add_smul,← Complex.ofReal_add,sub_add_cancel,Complex.ofReal_one,one_smul]

/-- The PPT overlap bound survives exact TP smoothing with the full-diamond factor 1/2. -/
theorem isometry_smoothed_lower (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (F : Set (MatrixMap a b)) (hPPT : ∀ M : KrausChannel a b, M.toLinearMap ∈ F → IsPPT M.toLinearMap)
    (δ : ℝ) (hδ : 0≤δ) :
    (Real.logb 2 (max 1 ((a:ℝ)*(1-δ/2))):EReal) ≤ smoothedResourceMax (isometryChannel J hJ) F δ := by
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hmax : 0<max 1 ((a:ℝ)*(1-δ/2)) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply le_iInf; intro L
  apply le_iInf; intro S
  have hcost : ENNReal.ofReal (max 1 ((a:ℝ)*(1-δ/2))) ≤ dominationCost L.val S.val := by
    apply le_iInf; intro lam
    apply ENNReal.ofReal_le_ofReal
    apply max_le lam.property.1
    let T := isometryTestEffect J hJ ha
    let ψ := maximallyEntangledInput ha
    have hd := UniformAuxiliary.probability_sub_le_half_diamond (isometryChannel J hJ) L.val δ hδ L.property ψ T
    have hc := DiamondTesting.testValue_le_of_cpLe L.val.toLinearMap S.val lam.val lam.property.2 ψ T
    rw [DiamondTesting.testValue_channel] at hc
    change T.probability (normalizedChoiState (isometryChannel J hJ) ha)-T.probability (normalizedChoiState L.val ha)≤δ/2 at hd
    rw [isometryTestEffect_target] at hd
    have hq := isometryTestEffect_ppt_bound J hJ ha S.val (hPPT S.val S.property)
    have hl : 0≤lam.val := by linarith [lam.property.1]
    have hh := mul_le_mul_of_nonneg_left hq hl
    change T.probability (normalizedChoiState L.val ha) ≤ lam.val*T.probability (normalizedChoiState S.val ha) at hc
    dsimp [T] at hc hd
    have hx : 1-δ/2≤lam.val/(a:ℝ) := by
      change 1-δ/2≤lam.val*(a:ℝ)⁻¹
      linarith
    simpa only [mul_comm] using (le_div_iff₀ haR).mp hx
  have h := log2Cost_mono hcost
  rwa [log2Cost_ofReal _ hmax] at h


/-- Scalar interpolation giving the exact capped domination cost, including d=1. -/
theorem isometric_interpolation (d δ : ℝ) (hd : 1≤d) (hδ : 0≤δ) :
    ∃ s : ℝ, 0≤s ∧ s≤1 ∧ s*(2*(1-d⁻¹))≤δ ∧
      (1-s)*d+s=max 1 (d*(1-δ/2)) := by
  by_cases hd1 : d=1
  · refine ⟨0,le_rfl,by norm_num,by simpa using hδ,?_⟩
    rw [hd1]
    simp only [sub_zero,zero_mul,mul_one,add_zero,one_mul]
    exact (max_eq_left (by linarith)).symm
  have hdgt : 1<d := lt_of_le_of_ne hd (Ne.symm hd1)
  have hdp : 0<d := by linarith
  have hc : 0<2*(1-d⁻¹) := by
    have hi : d⁻¹<1 := (inv_lt_one₀ hdp).mpr (by linarith)
    linarith
  let s := min 1 (δ/(2*(1-d⁻¹)))
  have hs : 0≤s := le_min zero_le_one (div_nonneg hδ hc.le)
  have hs1 : s≤1 := min_le_left _ _
  have herr : s*(2*(1-d⁻¹))≤δ := (le_div_iff₀ hc).mp (min_le_right _ _)
  refine ⟨s,hs,hs1,herr,?_⟩
  by_cases hsmall : δ≤2*(1-d⁻¹)
  · have he : s=δ/(2*(1-d⁻¹)) := min_eq_right ((div_le_one hc).mpr hsmall)
    have hcost : (1-s)*d+s=d*(1-δ/2) := by
      have hs_eq : s*(2*(1-d⁻¹))=δ := by rw [he]; exact div_mul_cancel₀ _ hc.ne'
      have hh : s*(d-1)=δ*d/2 := by
        calc
          s*(d-1) = (s*(2*(1-d⁻¹)))*d/2 := by field_simp [hdp.ne']
          _ = δ*d/2 := by rw [hs_eq]
      nlinarith

    rw [hcost]
    apply (max_eq_right _).symm
    have hh := mul_le_mul_of_nonneg_left hsmall hdp.le
    have hinv : d*d⁻¹=1 := mul_inv_cancel₀ hdp.ne'
    nlinarith
  · have he : s=1 := min_eq_left ((one_le_div hc).mpr (le_of_lt (lt_of_not_ge hsmall)))
    rw [he]
    simp only [sub_self,zero_mul,zero_add]
    apply (max_eq_left _).symm
    have hh := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hsmall)) hdp.le
    have hinv : d*d⁻¹=1 := mul_inv_cancel₀ hdp.ne'
    nlinarith

/-- Construct a CPTP smoothing witness attaining the exact cost. -/
theorem isometry_smoothed_upper (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (F : Set (MatrixMap a b)) (hfree : (pinchedIsometry J hJ).toLinearMap ∈ F)
    (δ : ℝ) (hδ : 0≤δ) :
    smoothedResourceMax (isometryChannel J hJ) F δ ≤
      (Real.logb 2 (max 1 ((a:ℝ)*(1-δ/2))):EReal) := by
  let N := isometryChannel J hJ
  let M := pinchedIsometry J hJ
  have had : (1:ℝ)≤a := by exact_mod_cast ha
  obtain ⟨s,hs,hs1,herr,hcost⟩ := isometric_interpolation (a:ℝ) δ had hδ
  obtain ⟨L,hL⟩ := exists_channel_mixture N M s hs hs1
  have hdom : MatrixMap.CPLe L.toLinearMap ((((1-s)*(a:ℝ)+s:ℝ):ℂ) • M.toLinearMap) := by
    have h := MatrixMap.completelyPositive_smul (sub_nonneg.mpr hs1) (isometry_cpLe_pinched J hJ)
    have he : ((((1-s)*(a:ℝ)+s:ℝ):ℂ) • M.toLinearMap)-L.toLinearMap =
        ((1-s:ℝ):ℂ) • ((a:ℂ) • M.toLinearMap-N.toLinearMap) := by
      rw [hL]
      push_cast
      module
    change MatrixMap.CompletelyPositive (_-_)
    rw [he]
    exact h
  have hclose : diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ := by
    have he : L.toLinearMap-N.toLinearMap=(s:ℂ) • (M.toLinearMap-N.toLinearMap) := by
      rw [hL]
      push_cast
      module
    rw [he]
    have hc : 0≤2*(1-(a:ℝ)⁻¹) := by
      exact mul_nonneg (by norm_num) (sub_nonneg.mpr (inv_le_one_of_one_le₀ had))
    exact (diamondNorm_smul_le _ s _ hs hc (diamond_distance_of_domination N M (a:ℝ) had
      (isometry_cpLe_pinched J hJ))).trans (ENNReal.ofReal_le_ofReal herr)
  have hlam : 1≤(1-s)*(a:ℝ)+s := by rw [hcost]; exact le_max_left _ _
  have h := smoothedResourceMax_le_of_witness N L M F hfree ((1-s)*(a:ℝ)+s) δ hlam hdom hclose
  rwa [hcost] at h

/-- Exact one-block CPTP-smoothed resource value for every diamond radius. -/
theorem isometry_smoothed_exact (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (F : Set (MatrixMap a b)) (hfree : (pinchedIsometry J hJ).toLinearMap ∈ F)
    (hPPT : ∀ M : KrausChannel a b, M.toLinearMap ∈ F → IsPPT M.toLinearMap)
    (δ : ℝ) (hδ : 0≤δ) :
    smoothedResourceMax (isometryChannel J hJ) F δ =
      (Real.logb 2 (max 1 ((a:ℝ)*(1-δ/2))):EReal) :=
  le_antisymm (isometry_smoothed_upper J hJ ha F hfree δ hδ)
    (isometry_smoothed_lower J hJ ha F hPPT δ hδ)


theorem smoothedResourceMax_congr_target {N L : KrausChannel a b} (h : N.toLinearMap=L.toLinearMap)
    (F : Set (MatrixMap a b)) (δ : ℝ) : smoothedResourceMax N F δ=smoothedResourceMax L F δ := by
  unfold smoothedResourceMax
  rw [h]

/-- Corollary 23, for both full EB and PPT alternatives and the full diamond norm.
The dimension-one case is included in the proved scalar interpolation lemma. -/
theorem corollary_23 (J : Matrix (Fin b) (Fin a) ℂ) (hJ : Jᴴ*J=1) (ha : 0<a)
    (n : ℕ) (δ : ℝ) (hδ : 0≤δ) (hδ2 : δ≤2) :
    smoothedResourceMax ((isometryChannel J hJ).tensorPower n) (EBFamily a b n) δ =
      (Real.logb 2 (max 1 ((a:ℝ)^n*(1-δ/2))):EReal) ∧
    smoothedResourceMax ((isometryChannel J hJ).tensorPower n) (PPTFamily a b n) δ =
      (Real.logb 2 (max 1 ((a:ℝ)^n*(1-δ/2))):EReal) := by
  let K := powerIsometry J n
  have hK := powerIsometry_isometry J hJ n
  have hN := isometryChannel_power_map J hJ n
  have he : (pinchedIsometry K hK).toLinearMap ∈ EBFamily a b n :=
    (mem_EBFamily_iff n _).mpr (pinchedIsometry_EB K hK)
  have hp : (pinchedIsometry K hK).toLinearMap ∈ PPTFamily a b n := EBFamily_subset_PPTFamily n he
  have hall : ∀ M : KrausChannel (a^n) (b^n), M.toLinearMap ∈ PPTFamily a b n → IsPPT M.toLinearMap :=
    fun M hM => hM.2
  have hallE : ∀ M : KrausChannel (a^n) (b^n), M.toLinearMap ∈ EBFamily a b n → IsPPT M.toLinearMap :=
    fun M hM => (EBFamily_subset_PPTFamily n hM).2
  rw [smoothedResourceMax_congr_target hN,smoothedResourceMax_congr_target hN]
  simpa only [Nat.cast_pow] using And.intro
    (isometry_smoothed_exact K hK (pow_pos ha n) _ he hallE δ hδ)
    (isometry_smoothed_exact K hK (pow_pos ha n) _ hp hall δ hδ)

end GeneralizedChannelStein
