import GeneralizedChannelStein.CPTPAEP
import GeneralizedChannelStein.ChannelSpace
import GeneralizedChannelStein.TensorStateLowerBound
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! # Attainment of actual CP domination and exact-CPTP diamond smoothing

Compactness is in literal Choi coordinates. The diamond sublevel set uses
all finite references and arbitrary trace-norm-unit-ball matrices.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace GeneralizedChannelStein.SmoothingAttainment
open QuantumChannelStein Matrix TestingSDP DiamondNorm TraceNorm
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
variable {a b : ℕ}

/-- The actual linear map reconstructed from any Choi matrix. -/
def fromChoi (C : BipartiteOperator a b) : MatrixMap a b where
  toFun := choiAction C
  map_add' X Y := by ext i j; simp [choiAction,add_mul,Finset.sum_add_distrib]
  map_smul' c X := by ext i j; simp [choiAction,Finset.mul_sum,mul_assoc]

@[simp] theorem fromChoi_choi (Φ : MatrixMap a b) : fromChoi (MatrixMap.choi Φ)=Φ := by
  ext X i j
  exact congrFun (congrFun (choiAction_choi Φ X) i) j

@[simp] theorem choi_fromChoi (C : BipartiteOperator a b) : MatrixMap.choi (fromChoi C)=C := by
  ext ⟨i,u⟩ ⟨j,v⟩
  simp [MatrixMap.choi,fromChoi,choiAction,Matrix.single,ite_and]

/-- Continuity is proved for the trace-square-root definition, not assumed. -/
theorem continuous_traceNorm (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Continuous (TraceNorm.traceNorm : Matrix ι ι ℂ → ℝ) := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  have hs : Continuous (fun X : Matrix ι ι ℂ => CFC.sqrt (Xᴴ*X)) := by
    apply CFC.continuousOn_sqrt.comp_continuous (by fun_prop)
    intro X
    exact (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  have ht : Continuous (fun X : Matrix ι ι ℂ => X.trace.re) := by
    unfold Matrix.trace Matrix.diag
    fun_prop
  exact ht.comp hs

/-- The literal full-diamond ball in finite-dimensional Choi coordinates. -/
def diamondChoiBall (N : KrausChannel a b) (δ : ℝ) : Set (BipartiteOperator a b) :=
  {C | diamondNorm (fromChoi C-N.toLinearMap) ≤ ENNReal.ofReal δ}

theorem isClosed_diamondChoiBall (N : KrausChannel a b) (δ : ℝ) :
    IsClosed (diamondChoiBall N δ) := by
  have heq : diamondChoiBall N δ =
      ⋂ r : ℕ, ⋂ X : {X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ // TraceNorm.traceNorm X ≤ 1},
        {C | ENNReal.ofReal (TraceNorm.traceNorm (MatrixMap.amplify (fromChoi C-N.toLinearMap) r X.val)) ≤
          ENNReal.ofReal δ} := by
    ext C
    simp only [diamondChoiBall,Set.mem_setOf_eq,diamondNorm,iSup_le_iff,Set.mem_iInter]
  rw [heq]
  apply isClosed_iInter; intro r
  apply isClosed_iInter; intro X
  apply isClosed_le _ continuous_const
  apply ENNReal.continuous_ofReal.comp
  apply (continuous_traceNorm (Fin r × Fin b)).comp
  unfold MatrixMap.amplify
  simp only [LinearMap.sub_apply,fromChoi,LinearMap.coe_mk,AddHom.coe_mk,Matrix.sub_apply]
  unfold choiAction
  fun_prop

/-- The exact-CPTP diamond ball is compact, including radius zero. -/
theorem isCompact_channelDiamondBall (N : KrausChannel a b) (δ : ℝ) :
    IsCompact (channelChoiSet a b ∩ diamondChoiBall N δ) :=
  (isCompact_channelChoiSet a b).inter_right (isClosed_diamondChoiBall N δ)

/-- A compact set of actual matrix pairs has a smallest feasible CP scalar
whenever one finite witness exists. No entropy or smoothing infimum is assumed. -/
theorem exists_minimal_scalar (K : Set (BipartiteOperator a b × BipartiteOperator a b))
    (hK : IsCompact K) (X₀ Y₀ : BipartiteOperator a b) (hXY₀ : (X₀,Y₀) ∈ K)
    (B : ℝ) (hB : 1 ≤ B) (hdom₀ : (B • Y₀-X₀).PosSemidef) :
    ∃ X Y : BipartiteOperator a b, ∃ c : ℝ,
      (X,Y) ∈ K ∧ 1 ≤ c ∧ (c • Y-X).PosSemidef ∧
      ∀ X' Y' : BipartiteOperator a b, (X',Y') ∈ K → ∀ c' : ℝ,
        1 ≤ c' → (c' • Y'-X').PosSemidef → c ≤ c' := by
  let S := (K ×ˢ Set.Icc (1:ℝ) B) ∩
    {z : (BipartiteOperator a b × BipartiteOperator a b) × ℝ |
      (z.2 • z.1.2-z.1.1).PosSemidef}
  have hclosed : IsClosed {z : (BipartiteOperator a b × BipartiteOperator a b) × ℝ |
      (z.2 • z.1.2-z.1.1).PosSemidef} := by
    letI : CStarAlgebra (BipartiteOperator a b) := CStarAlgebra.mk
    have h : IsClosed {z : (BipartiteOperator a b × BipartiteOperator a b) × ℝ |
        0 ≤ z.2 • z.1.2-z.1.1} :=
      isClosed_le continuous_const (continuous_snd.smul continuous_fst.snd |>.sub continuous_fst.fst)
    simpa only [Matrix.nonneg_iff_posSemidef] using h
  have hcompact : IsCompact S := (hK.prod isCompact_Icc).inter_right hclosed
  have hnonempty : S.Nonempty := ⟨((X₀,Y₀),B),⟨⟨hXY₀,hB,le_rfl⟩,hdom₀⟩⟩
  obtain ⟨z,hz,hmin⟩ := hcompact.exists_isMinOn hnonempty (continuous_snd.continuousOn)
  refine ⟨z.1.1,z.1.2,z.2,hz.1.1,hz.1.2.1,hz.2,?_⟩
  intro X' Y' hXY c' hc' hdom
  by_cases hcb : c' ≤ B
  · have hz' : ((X',Y'),c') ∈ S := ⟨⟨hXY,hc',hcb⟩,hdom⟩
    exact hmin hz'
  · exact hz.1.2.2.trans (le_of_not_ge hcb)



/-- The scalar Choi constraint is exactly the original CP-order constraint. -/
theorem cpLe_iff_choi_scalar (L S : KrausChannel a b) (c : ℝ) :
    MatrixMap.CPLe L.toLinearMap ((c:ℂ) • S.toLinearMap) ↔
      (c • S.choi-L.choi).PosSemidef := by
  rw [MatrixMap.cpLe_iff_choi_difference,MatrixMap.choi_smul]
  simp only [MatrixMap.choi_toLinearMap]
  have hs : (c:ℂ) • S.choi=c • S.choi := by ext i j; simp [Complex.real_smul]
  rw [hs]

/-- An absent finite domination witness is represented by infinity. -/
theorem dominationCost_eq_top_iff (L S : KrausChannel a b) :
    dominationCost L S = ⊤ ↔
      ¬ ∃ c : ℝ, 1 ≤ c ∧ MatrixMap.CPLe L.toLinearMap ((c:ℂ) • S.toLinearMap) := by
  constructor
  · intro h ⟨c,hc,hd⟩
    have hb : dominationCost L S ≤ ENNReal.ofReal c := iInf_le_of_le ⟨c,hc,hd⟩ le_rfl
    rw [h] at hb
    exact (not_le_of_gt ENNReal.ofReal_lt_top) hb
  · intro h
    apply top_le_iff.mp
    apply le_iInf
    intro c
    exact (h ⟨c.val,c.property⟩).elim

/-- Identifies the literal ENNReal infimum from an actual smallest scalar. -/
theorem dominationCost_eq_of_minimum (L S : KrausChannel a b) (c : ℝ) (hc : 1 ≤ c)
    (hd : MatrixMap.CPLe L.toLinearMap ((c:ℂ) • S.toLinearMap))
    (hmin : ∀ c' : ℝ, 1 ≤ c' → MatrixMap.CPLe L.toLinearMap ((c':ℂ) • S.toLinearMap) → c ≤ c') :
    dominationCost L S=ENNReal.ofReal c := by
  apply le_antisymm
  · exact iInf_le_of_le ⟨c,hc,hd⟩ le_rfl
  · apply le_iInf
    intro c'
    exact ENNReal.ofReal_le_ofReal (hmin c'.val c'.property.1 c'.property.2)

/-- Fixed-pair cost is attained exactly in its finite branch. -/
theorem exists_dominationCost_minimizer (L S : KrausChannel a b)
    (hfinite : dominationCost L S ≠ ⊤) :
    ∃ c : ℝ, 1 ≤ c ∧ MatrixMap.CPLe L.toLinearMap ((c:ℂ) • S.toLinearMap) ∧
      dominationCost L S=ENNReal.ofReal c := by
  have hex : ∃ c : ℝ, 1 ≤ c ∧ MatrixMap.CPLe L.toLinearMap ((c:ℂ) • S.toLinearMap) := by
    by_contra h
    exact hfinite ((dominationCost_eq_top_iff L S).mpr h)
  obtain ⟨B,hB,hdB⟩ := hex
  obtain ⟨X,Y,c,hXY,hc,hd,hmin⟩ := exists_minimal_scalar
    {(L.choi,S.choi)} isCompact_singleton L.choi S.choi (by simp) B hB
    ((cpLe_iff_choi_scalar L S B).mp hdB)
  have heq := Set.mem_singleton_iff.mp hXY
  have hX := congrArg Prod.fst heq
  have hY := congrArg Prod.snd heq
  change X=L.choi at hX
  change Y=S.choi at hY
  subst X; subst Y
  have hd' := (cpLe_iff_choi_scalar L S c).mpr hd
  refine ⟨c,hc,hd',dominationCost_eq_of_minimum L S c hc hd' ?_⟩
  intro c' hc' hd'
  exact hmin L.choi S.choi (by simp) c' hc' ((cpLe_iff_choi_scalar L S c').mp hd')

/-- A simultaneous scalar lower bound passes through both literal infima and the extended logarithm. -/
theorem log_le_resourceMax_of_scalar_lower (L : KrausChannel a b)
    (F : Set (MatrixMap a b)) (c : ℝ) (hc : 0 < c)
    (hmin : ∀ S : FreeChannel F, ∀ c' : ℝ, 1 ≤ c' →
      MatrixMap.CPLe L.toLinearMap ((c':ℂ) • S.val.toLinearMap) → c ≤ c') :
    (Real.logb 2 c:EReal) ≤ resourceMax L F := by
  apply le_iInf
  intro S
  have hcost : ENNReal.ofReal c ≤ dominationCost L S.val := by
    apply le_iInf
    intro c'
    exact ENNReal.ofReal_le_ofReal (hmin S c'.val c'.property.1 c'.property.2)
  have h := log2Cost_mono hcost
  rwa [log2Cost_ofReal c hc] at h

/-- A compact free family has an actual minimizing dominator whenever it
contains one finite dominator of the target. -/
theorem exists_resourceMax_minimizer (L : KrausChannel a b) (F : Set (MatrixMap a b))
    (hcompact : IsCompact (MatrixMap.choi '' F))
    (hchannels : ∀ Φ ∈ F, IsChannel Φ)
    (S₀ : KrausChannel a b) (hS₀ : S₀.toLinearMap ∈ F)
    (B : ℝ) (hB : 1 ≤ B)
    (hdom₀ : MatrixMap.CPLe L.toLinearMap ((B:ℂ) • S₀.toLinearMap)) :
    ∃ S : KrausChannel a b, ∃ c : ℝ, S.toLinearMap ∈ F ∧ 1 ≤ c ∧
      MatrixMap.CPLe L.toLinearMap ((c:ℂ) • S.toLinearMap) ∧
      dominationCost L S=ENNReal.ofReal c ∧
      resourceMax L F=(Real.logb 2 c:EReal) ∧ c ≤ B := by
  let K := ({L.choi} : Set (BipartiteOperator a b)) ×ˢ (MatrixMap.choi '' F)
  obtain ⟨X,Y,c,hXY,hc,hd,hmin⟩ := exists_minimal_scalar K (isCompact_singleton.prod hcompact)
    L.choi S₀.choi ⟨by simp,⟨S₀.toLinearMap,hS₀,rfl⟩⟩ B hB
      ((cpLe_iff_choi_scalar L S₀ B).mp hdom₀)
  have hX : X=L.choi := Set.mem_singleton_iff.mp hXY.1
  subst X
  obtain ⟨Φ,hΦ,hY⟩ := hXY.2
  obtain ⟨S,hS⟩ := (isChannel_iff_kraus Φ).mp (hchannels Φ hΦ)
  have hSmem : S.toLinearMap ∈ F := hS ▸ hΦ
  have hSY : S.choi=Y := by rw [← MatrixMap.choi_toLinearMap,hS,hY]
  subst Y
  have hd' := (cpLe_iff_choi_scalar L S c).mpr hd
  have hmin' (S' : KrausChannel a b) (hS' : S'.toLinearMap ∈ F) (c' : ℝ)
      (hc' : 1 ≤ c') (hd' : MatrixMap.CPLe L.toLinearMap ((c':ℂ) • S'.toLinearMap)) : c ≤ c' :=
    hmin L.choi S'.choi ⟨by simp,⟨S'.toLinearMap,hS',rfl⟩⟩ c' hc'
      ((cpLe_iff_choi_scalar L S' c').mp hd')
  refine ⟨S,c,hSmem,hc,hd',dominationCost_eq_of_minimum L S c hc hd' (hmin' S hSmem),?_,
    hmin' S₀ hS₀ B hB hdom₀⟩
  apply le_antisymm
  · exact resourceMax_le_of_domination L S F hSmem c hc hd'
  · exact log_le_resourceMax_of_scalar_lower L F c (by linarith) (fun S' => hmin' S'.val S'.property)



/-- Exact-CPTP smoothing attains a single approximant, free dominator, and
scalar simultaneously, including the zero-radius ball. -/
theorem exists_smoothedResourceMax_minimizer (N : KrausChannel a b)
    (F : Set (MatrixMap a b)) (hcompact : IsCompact (MatrixMap.choi '' F))
    (hchannels : ∀ Φ ∈ F, IsChannel Φ)
    (S₀ : KrausChannel a b) (hS₀ : S₀.toLinearMap ∈ F)
    (B : ℝ) (hB : 1 ≤ B)
    (hdom₀ : MatrixMap.CPLe N.toLinearMap ((B:ℂ) • S₀.toLinearMap)) (δ : ℝ) :
    ∃ L S : KrausChannel a b, ∃ c : ℝ,
      diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ ∧
      S.toLinearMap ∈ F ∧ 1 ≤ c ∧
      MatrixMap.CPLe L.toLinearMap ((c:ℂ) • S.toLinearMap) ∧
      dominationCost L S=ENNReal.ofReal c ∧
      resourceMax L F=(Real.logb 2 c:EReal) ∧
      smoothedResourceMax N F δ=(Real.logb 2 c:EReal) ∧ c ≤ B := by
  let K := (channelChoiSet a b ∩ diamondChoiBall N δ) ×ˢ (MatrixMap.choi '' F)
  have hN : N.choi ∈ channelChoiSet a b ∩ diamondChoiBall N δ := by
    refine ⟨⟨N.choi_positive,N.traceOutput_choi⟩,?_⟩
    change diamondNorm (fromChoi (MatrixMap.choi N.toLinearMap)-N.toLinearMap) ≤ _
    rw [fromChoi_choi,sub_self,zero_diamondNorm]
    exact zero_le _
  obtain ⟨X,Y,c,hXY,hc,hd,hmin⟩ := exists_minimal_scalar K
    ((isCompact_channelDiamondBall N δ).prod hcompact) N.choi S₀.choi
    ⟨hN,⟨S₀.toLinearMap,hS₀,rfl⟩⟩ B hB ((cpLe_iff_choi_scalar N S₀ B).mp hdom₀)
  obtain ⟨L,hL⟩ := (KrausChannel.is_choi_iff X).mpr hXY.1.1
  have hclose : diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ := by
    have h := hXY.1.2
    change diamondNorm (fromChoi X-N.toLinearMap) ≤ _ at h
    rw [← hL,← MatrixMap.choi_toLinearMap,fromChoi_choi] at h
    exact h
  obtain ⟨Φ,hΦ,hY⟩ := hXY.2
  obtain ⟨S,hS⟩ := (isChannel_iff_kraus Φ).mp (hchannels Φ hΦ)
  have hSmem : S.toLinearMap ∈ F := hS ▸ hΦ
  have hSY : S.choi=Y := by rw [← MatrixMap.choi_toLinearMap,hS,hY]
  have hd' : MatrixMap.CPLe L.toLinearMap ((c:ℂ) • S.toLinearMap) := by
    apply (cpLe_iff_choi_scalar L S c).mpr
    rwa [hL,hSY]
  have hmin' (L' S' : KrausChannel a b)
      (hclose' : diamondNorm (L'.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ)
      (hS' : S'.toLinearMap ∈ F) (c' : ℝ) (hc' : 1 ≤ c')
      (hd' : MatrixMap.CPLe L'.toLinearMap ((c':ℂ) • S'.toLinearMap)) : c ≤ c' := by
    have hL' : L'.choi ∈ channelChoiSet a b ∩ diamondChoiBall N δ := by
      refine ⟨⟨L'.choi_positive,L'.traceOutput_choi⟩,?_⟩
      change diamondNorm (fromChoi (MatrixMap.choi L'.toLinearMap)-N.toLinearMap) ≤ _
      rwa [fromChoi_choi]
    exact hmin L'.choi S'.choi ⟨hL',⟨S'.toLinearMap,hS',rfl⟩⟩ c' hc'
      ((cpLe_iff_choi_scalar L' S' c').mp hd')
  have hresource : resourceMax L F=(Real.logb 2 c:EReal) := by
    apply le_antisymm
    · exact resourceMax_le_of_domination L S F hSmem c hc hd'
    · exact log_le_resourceMax_of_scalar_lower L F c (by linarith)
        (fun S' => hmin' L S'.val hclose S'.property)
  refine ⟨L,S,c,hclose,hSmem,hc,hd',
    dominationCost_eq_of_minimum L S c hc hd' (hmin' L S hclose hSmem),hresource,?_,
    hmin N.choi S₀.choi ⟨hN,⟨S₀.toLinearMap,hS₀,rfl⟩⟩ B hB
      ((cpLe_iff_choi_scalar N S₀ B).mp hdom₀)⟩
  apply le_antisymm
  · exact smoothedResourceMax_le_of_witness N L S F hSmem c δ hc hd' hclose
  · apply le_iInf
    intro L'
    exact log_le_resourceMax_of_scalar_lower L'.val F c (by linarith)
      (fun S' => hmin' L'.val S'.val L'.property S'.property)



/-- The paragraph preceding Theorem 11 uses the Choi trace bound a/w,
rather than the different output-dimension rate needed by Lemma 4. -/
theorem cpLe_replacer_input_bound (L : KrausChannel a b) (ω : State b)
    (w : ℝ) (hw : 0 < w) (hω : (ω.matrix-w•(1:Operator b)).PosSemidef) :
    MatrixMap.CPLe L.toLinearMap (((((a:ℝ)/w:ℝ):ℂ)) • (ReplacerChannel.channel a ω).toLinearMap) := by
  rw [MatrixMap.cpLe_iff_choi_difference,MatrixMap.choi_smul,
    MatrixMap.choi_toLinearMap,MatrixMap.choi_toLinearMap,ReplacerChannel.channel_choi]
  have hp := (MatrixMap.posSemidef_kronecker (Matrix.PosSemidef.one (n := Fin a)) hω).smul
    (div_nonneg (Nat.cast_nonneg a) hw.le)
  have ht : L.choi.trace=(a:ℂ) := channelChoiSet_trace ⟨L.choi_positive,L.traceOutput_choi⟩
  have hq : ((a:ℝ) • (1:BipartiteOperator a b)-L.choi).PosSemidef := by
    have h := positive_le_trace_smul_one L.choi_positive
    simpa only [ht,Complex.natCast_re] using h
  convert hp.add hq using 1
  ext ⟨i,u⟩ ⟨j,v⟩
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.kroneckerMap_apply,
    Complex.real_smul,smul_eq_mul,Matrix.one_apply]
  push_cast
  split_ifs <;> simp_all <;> field_simp <;> ring

/-- Every actual n-block channel has the paper's finite faithful-replacer
bound, even when that block channel has arbitrary correlations. -/
theorem admissible_finite_dominator (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0 < n) (L : KrausChannel (a^n) (b^n)) :
    let w := DimensionDomination.minEigenvalue ω hb
    let B := ((a:ℝ)/w)^n
    1 ≤ B ∧
      ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap ∈ F n ∧
      MatrixMap.CPLe L.toLinearMap ((B:ℂ) • ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap) := by
  dsimp only
  let w := DimensionDomination.minEigenvalue ω hb
  have hw : 0 < w := DimensionDomination.minEigenvalue_pos ω hb hω
  have hw1 : w ≤ 1 := DimensionDomination.minEigenvalue_le_one ω hb
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hB : 1 ≤ ((a:ℝ)/w)^n := one_le_pow₀ ((le_div_iff₀ hw).mpr (by linarith))
  have hpow := TensorStateLowerBound.statePower_lower ω w hw.le
    (DimensionDomination.scalar_le_of_eigenvalue_lower ω w (DimensionDomination.minEigenvalue_le ω hb)) n
  have hdom := cpLe_replacer_input_bound L (PerfectDiscrimination.statePower ω n) (w^n) (pow_pos hw n) hpow
  have hmap : (ReplacerChannel.channel (a^n) (PerfectDiscrimination.statePower ω n)).toLinearMap =
      ((ReplacerChannel.channel a ω).tensorPower n).toLinearMap := by
    rw [ReplacerChannel.channel_map,ReplacerChannel.tensorPower_map]
  rw [hmap] at hdom
  have heq : ((a^n:ℕ):ℝ)/(w^n)=((a:ℝ)/w)^n := by rw [Nat.cast_pow,div_pow]
  rw [heq] at hdom
  exact ⟨hB,replacer_power_mem F hF.tensor_closed ω hOne n hn,hdom⟩

/-- Literal resource-max attainment for every positive block and every
actual block channel, under F1--F3 alone. -/
theorem resourceMax_attained (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0 < n) (L : KrausChannel (a^n) (b^n)) :
    ∃ S : KrausChannel (a^n) (b^n), ∃ c : ℝ,
      S.toLinearMap ∈ F n ∧ 1 ≤ c ∧
      MatrixMap.CPLe L.toLinearMap ((c:ℂ) • S.toLinearMap) ∧
      dominationCost L S=ENNReal.ofReal c ∧ resourceMax L (F n)=(Real.logb 2 c:EReal) ∧
      c ≤ ((a:ℝ)/DimensionDomination.minEigenvalue ω hb)^n := by
  obtain ⟨hB,hR,hdom⟩ := admissible_finite_dominator ha hb F hF ω hω hOne n hn L
  exact exists_resourceMax_minimizer L (F n) (hF.compact n hn) (hF.channels n hn)
    ((ReplacerChannel.channel a ω).tensorPower n) hR _ hB hdom

/-- Literal exact-CPTP diamond-smoothing attainment for every nonnegative
radius, including zero, with the exact paper finite scalar bound. -/
theorem smoothedResourceMax_attained (ha : 0 < a) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0 < n) (N : KrausChannel (a^n) (b^n)) (δ : ℝ) (_hδ : 0 ≤ δ) :
    ∃ L S : KrausChannel (a^n) (b^n), ∃ c : ℝ,
      diamondNorm (L.toLinearMap-N.toLinearMap) ≤ ENNReal.ofReal δ ∧
      S.toLinearMap ∈ F n ∧ 1 ≤ c ∧
      MatrixMap.CPLe L.toLinearMap ((c:ℂ) • S.toLinearMap) ∧
      dominationCost L S=ENNReal.ofReal c ∧ resourceMax L (F n)=(Real.logb 2 c:EReal) ∧
      smoothedResourceMax N (F n) δ=(Real.logb 2 c:EReal) ∧
      c ≤ ((a:ℝ)/DimensionDomination.minEigenvalue ω hb)^n := by
  obtain ⟨hB,hR,hdom⟩ := admissible_finite_dominator ha hb F hF ω hω hOne n hn N
  exact exists_smoothedResourceMax_minimizer N (F n) (hF.compact n hn) (hF.channels n hn)
    ((ReplacerChannel.channel a ω).tensorPower n) hR _ hB hdom δ

end GeneralizedChannelStein.SmoothingAttainment
