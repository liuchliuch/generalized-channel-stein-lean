import GeneralizedChannelStein.CanonicalAttainment
import GeneralizedChannelStein.ChannelSpace
import GeneralizedChannelStein.TestingMinimax

/-! Actual faithful-regularized canonical entropy games on Choi space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CanonicalRegularization
open QuantumChannelStein Matrix ChannelEntropy RelativeEntropy CanonicalInput CanonicalAttainment
open EntropyFlags DominatedEntropyContinuity
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Topology
variable {n m : ℕ}

def choiChannel (C : channelChoiSet n m) : KrausChannel n m :=
  Classical.choose ((KrausChannel.is_choi_iff C.val).mpr C.property)

@[simp] theorem choiChannel_choi (C : channelChoiSet n m) : (choiChannel C).choi=C.val :=
  Classical.choose_spec ((KrausChannel.is_choi_iff C.val).mpr C.property)

def regChoi (R : KrausChannel n m) (δ : ℝ) (C : Matrix (Fin n×Fin m) (Fin n×Fin m) ℂ) :=
  (1-δ)•C+δ•R.choi

theorem regChoi_mem (R : KrausChannel n m) (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1)
    (C : channelChoiSet n m) : regChoi R δ C.val∈channelChoiSet n m := by
  exact convex_channelChoiSet n m C.property ⟨R.choi_positive,R.traceOutput_choi⟩
    (sub_nonneg.mpr hδ1) hδ (by ring)

def regChannel (R : KrausChannel n m) (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1)
    (C : channelChoiSet n m) : KrausChannel n m := choiChannel ⟨regChoi R δ C.val,regChoi_mem R δ hδ hδ1 C⟩

@[simp] theorem regChannel_choi (R : KrausChannel n m) (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1)
    (C : channelChoiSet n m) : (regChannel R δ hδ hδ1 C).choi=regChoi R δ C.val := choiChannel_choi _

theorem regChannel_map (R : KrausChannel n m) (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1)
    (C : channelChoiSet n m) :
    (regChannel R δ hδ hδ1 C).toLinearMap = ((1-δ:ℝ):ℂ)•(choiChannel C).toLinearMap+(δ:ℂ)•R.toLinearMap := by
  apply MatrixMap.choi_injective
  rw [MatrixMap.choi_toLinearMap,regChannel_choi,MatrixMap.choi_add,MatrixMap.choi_smul,MatrixMap.choi_smul,
    MatrixMap.choi_toLinearMap,MatrixMap.choi_toLinearMap,choiChannel_choi]
  ext i j
  simp [regChoi,Complex.real_smul]

theorem replacer_component (R : KrausChannel n m) (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1)
    (C : channelChoiSet n m) :
    MatrixMap.CPLe ((δ:ℂ)•R.toLinearMap) (regChannel R δ hδ hδ1 C).toLinearMap := by
  rw [MatrixMap.cpLe_iff_choi_difference,MatrixMap.choi_toLinearMap,regChannel_choi,
    MatrixMap.choi_smul,MatrixMap.choi_toLinearMap]
  convert C.property.1.smul (sub_nonneg.mpr hδ1) using 1
  ext i j
  simp [regChoi,Complex.real_smul]

theorem target_domination (N R : KrausChannel n m) (c δ : ℝ) (hc : 0≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (C : channelChoiSet n m) :
    MatrixMap.CPLe N.toLinearMap (((c/δ:ℝ):ℂ)•(regChannel R δ hδ.le hδ1 C).toLinearMap) :=
  cpLe_of_positive_component N R _ c δ hc hδ hNR (replacer_component R δ hδ.le hδ1 C)

/-- Unbundled Choi congruence; outside density/channel sets it is only an
algebraic extension, never asserted to be a state. -/
def rawOutput (X : Operator n) (C : Matrix (Fin n×Fin m) (Fin n×Fin m) ℂ) : Operator (n*m) :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    ((CFC.sqrt Xᵀ⊗ₖ(1:Operator m))*C*(CFC.sqrt Xᵀ⊗ₖ(1:Operator m))ᴴ)

def game (N R : KrausChannel n m) (δ : ℝ) (X : Operator n)
    (C : Matrix (Fin n×Fin m) (Fin n×Fin m) ℂ) : ℝ :=
  rawFormula (rawOutput X N.choi) (rawOutput X (regChoi R δ C))

theorem game_eq_finiteValue (N R : KrausChannel n m) (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1)
    (ρ : densitySet n) (C : channelChoiSet n m) :
    game N R δ ρ.val C.val=finiteValue N (regChannel R δ hδ hδ1 C) ρ := by
  rw [finiteValue,← rawFormula_state,output_matrix,output_matrix,regChannel_choi]
  rfl

theorem value_eq_game (N R : KrausChannel n m) (c δ : ℝ) (hc : 0≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (ρ : densitySet n) (C : channelChoiSet n m) :
    value N (regChannel R δ hδ.le hδ1 C) (ofDensity ρ)=(game N R δ ρ.val C.val:EReal) := by
  rw [game_eq_finiteValue N R δ hδ.le hδ1]
  exact value_eq_finiteValue N _ (c/δ) (target_domination N R c δ hc hδ hδ1 hNR C) ρ

def regPair (N R : KrausChannel n m) (c δ : ℝ) (hc : 0≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap))
    (z : densitySet n×channelChoiSet n m) : dominatedPairs (n*m) (c/δ) :=
  canonicalPair N (regChannel R δ hδ.le hδ1 z.2) (c/δ)
    (target_domination N R c δ hc hδ hδ1 hNR z.2) z.1

theorem continuous_regPair (N R : KrausChannel n m) (c δ : ℝ) (hc : 0≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) :
    Continuous (regPair N R c δ hc hδ hδ1 hNR) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact (continuous_output_matrix N).comp continuous_fst
  · apply Continuous.subtype_mk
    have hC : Continuous (fun z : densitySet n×channelChoiSet n m => regChoi R δ z.2.val) := by
      unfold regChoi
      fun_prop
    have h := continuous_outputFromChoi.comp (continuous_fst.prodMk hC)
    convert h using 1
    funext z
    rw [output_matrix,regChannel_choi]
    rfl

theorem continuous_game (N R : KrausChannel n m) (c δ : ℝ) (hc : 0≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) :
    Continuous (fun z : densitySet n×channelChoiSet n m => game N R δ z.1.val z.2.val) := by
  have h := (continuous_traceFormula (n:=n*m) (c/δ) (div_nonneg hc hδ.le)).comp
    (continuous_regPair N R c δ hc hδ hδ1 hNR)
  convert h using 1
  funext z
  rw [game_eq_finiteValue N R δ hδ.le hδ1]
  simp only [Function.comp_def,regPair,canonicalPair,pairFirst,pairSecond,ofDensity_toDensity,finiteValue]

theorem game_nonneg (N R : KrausChannel n m) (c δ : ℝ) (hc : 0≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (ρ : densitySet n) (C : channelChoiSet n m) :
    0≤game N R δ ρ.val C.val := by
  have h := value_nonneg N (regChannel R δ hδ.le hδ1 C) (ofDensity ρ)
  rw [value_eq_game N R c δ hc hδ hδ1 hNR] at h
  exact EReal.coe_nonneg.mp h

theorem game_le_log (N R : KrausChannel n m) (c δ : ℝ) (hc : 1≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (ρ : densitySet n) (C : channelChoiSet n m) :
    game N R δ ρ.val C.val≤Real.logb 2 (c/δ) := by
  have hK : 1≤c/δ := (one_le_div hδ).mpr (hδ1.trans hc)
  have h := pureOutput_umegaki_le N (regChannel R δ hδ.le hδ1 C) (c/δ) hK
    (target_domination N R c δ (zero_le_one.trans hc) hδ hδ1 hNR C) (input (ofDensity ρ))
  change value N (regChannel R δ hδ.le hδ1 C) (ofDensity ρ)≤_ at h
  rw [value_eq_game N R c δ (zero_le_one.trans hc) hδ hδ1 hNR] at h
  exact EReal.coe_le_coe_iff.mp h

theorem game_concave_input (N R : KrausChannel n m) (c δ : ℝ) (hc : 0≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (C : channelChoiSet n m) :
    ConcaveOn ℝ (densitySet n) (fun X => game N R δ X C.val) := by
  refine ⟨convex_densitySet n,?_⟩
  intro X hX Y hY a b ha hb hab
  have ha1 : a≤1 := by linarith
  have heqb : b=1-a := by linarith
  let ρ : densitySet n := ⟨X,hX⟩
  let σ : densitySet n := ⟨Y,hY⟩
  let μ : densitySet n := ⟨a•X+b•Y,convex_densitySet n hX hY ha hb hab⟩
  have hm : EntropyContinuity.mix (ofDensity ρ) (ofDensity σ) a ha ha1=ofDensity μ := by
    apply state_eq_of_matrix_eq
    dsimp [EntropyContinuity.mix,ofDensity,ρ,σ,μ]
    rw [heqb]
  have h := CanonicalConcavity.value_concave_input N (regChannel R δ hδ.le hδ1 C)
    (ofDensity ρ) (ofDensity σ) a ha ha1
  rw [hm,value_eq_game N R c δ hc hδ hδ1 hNR,value_eq_game N R c δ hc hδ hδ1 hNR,
    value_eq_game N R c δ hc hδ hδ1 hNR,← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add] at h
  have h' := EReal.coe_le_coe_iff.mp h
  simpa only [ρ,σ,μ,heqb,smul_eq_mul] using h'

theorem regChannel_mix_map (R : KrausChannel n m) (δ : ℝ) (hδ : 0≤δ) (hδ1 : δ≤1)
    (C D : channelChoiSet n m) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    (regChannel R δ hδ hδ1
      ⟨p•C.val+(1-p)•D.val,convex_channelChoiSet n m C.property D.property hp (sub_nonneg.mpr hp1) (by ring)⟩).toLinearMap =
      (p:ℂ)•(regChannel R δ hδ hδ1 C).toLinearMap+((1-p:ℝ):ℂ)•(regChannel R δ hδ hδ1 D).toLinearMap := by
  apply MatrixMap.choi_injective
  simp only [MatrixMap.choi_add,MatrixMap.choi_smul,MatrixMap.choi_toLinearMap,regChannel_choi]
  ext i j
  simp only [regChoi,Matrix.add_apply,Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  push_cast
  ring

theorem game_convex_alternative (N R : KrausChannel n m) (c δ : ℝ) (hc : 0≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (ρ : densitySet n) :
    ConvexOn ℝ (channelChoiSet n m) (game N R δ ρ.val) := by
  refine ⟨convex_channelChoiSet n m,?_⟩
  intro C hC D hD a b ha hb hab
  have ha1 : a≤1 := by linarith
  have heqb : b=1-a := by linarith
  let C' : channelChoiSet n m := ⟨C,hC⟩
  let D' : channelChoiSet n m := ⟨D,hD⟩
  let B : channelChoiSet n m := ⟨a•C+(1-a)•D,convex_channelChoiSet n m hC hD ha (sub_nonneg.mpr ha1) (by ring)⟩
  have h := EntropyMinimax.value_convex_alternative_real N
    (regChannel R δ hδ.le hδ1 C') (regChannel R δ hδ.le hδ1 D') (regChannel R δ hδ.le hδ1 B)
    (ofDensity ρ) a ha ha1 (regChannel_mix_map R δ hδ.le hδ1 C' D' a ha ha1)
  rw [value_eq_game N R c δ hc hδ hδ1 hNR,value_eq_game N R c δ hc hδ hδ1 hNR,
    value_eq_game N R c δ hc hδ hδ1 hNR,← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add] at h
  have h' := EReal.coe_le_coe_iff.mp h
  simpa only [C',D',B,heqb,smul_eq_mul] using h'

theorem game_minimax (N R : KrausChannel n m) (c δ : ℝ) (hc : 1≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (hn : 0<n)
    (F : Set (Matrix (Fin n×Fin m) (Fin n×Fin m) ℂ))
    (hFcompact : IsCompact F) (hFconvex : Convex ℝ F) (hFne : F.Nonempty)
    (hFchannel : F⊆channelChoiSet n m) :
    (⨅ C : F, ⨆ ρ : densitySet n, game N R δ ρ.val C.val) =
      ⨆ ρ : densitySet n, ⨅ C : F, game N R δ ρ.val C.val := by
  have hcont := continuous_game N R c δ (zero_le_one.trans hc) hδ hδ1 hNR
  have hρne : (densitySet n).Nonempty := ⟨(FaithfulDensity.maximallyMixed n hn).matrix,
    (FaithfulDensity.maximallyMixed n hn).positive,(FaithfulDensity.maximallyMixed n hn).trace_one⟩
  apply sion_minimax (f:=fun C X => game N R δ X C) (S:=F) (T:=densitySet n)
  · intro X hX
    have hi : Continuous (fun C : channelChoiSet n m => ((⟨X,hX⟩ : densitySet n),C)) :=
      continuous_const.prodMk continuous_id
    have hh0 := hcont.comp hi
    have hh : Continuous (fun C : channelChoiSet n m => game N R δ X C.val) := by
      simpa only [Function.comp_def] using hh0
    have hh' : ContinuousOn (game N R δ X) (channelChoiSet n m) := by
      rw [continuousOn_iff_continuous_restrict]
      exact hh
    exact (hh'.mono hFchannel).lowerSemicontinuousOn
  · exact hFcompact
  · exact hFne
  · exact hρne
  · intro C hC
    have hi : Continuous (fun ρ : densitySet n => (ρ,(⟨C,hFchannel hC⟩ : channelChoiSet n m))) :=
      continuous_id.prodMk continuous_const
    have hh0 := hcont.comp hi
    have hh : Continuous (fun ρ : densitySet n => game N R δ ρ.val C) := by
      simpa only [Function.comp_def] using hh0
    have hh' : ContinuousOn (fun X => game N R δ X C) (densitySet n) := by
      rw [continuousOn_iff_continuous_restrict]
      exact hh
    exact hh'.upperSemicontinuousOn
  · intro X hX
    exact ((game_convex_alternative N R c δ (zero_le_one.trans hc) hδ hδ1 hNR ⟨X,hX⟩).subset hFchannel hFconvex).quasiconvexOn
  · intro C hC
    exact (game_concave_input N R c δ (zero_le_one.trans hc) hδ hδ1 hNR ⟨C,hFchannel hC⟩).quasiconcaveOn
  · exact convex_densitySet n
  · exact hFconvex
  · rw [← Set.image_prod]
    refine ⟨Real.logb 2 (c/δ),?_⟩
    rintro y ⟨⟨C,X⟩,⟨hC,hX⟩,rfl⟩
    exact game_le_log N R c δ hc hδ hδ1 hNR ⟨X,hX⟩ ⟨C,hFchannel hC⟩
  · rw [← Set.image_prod]
    refine ⟨0,?_⟩
    rintro y ⟨⟨C,X⟩,⟨hC,hX⟩,rfl⟩
    exact game_nonneg N R c δ (zero_le_one.trans hc) hδ hδ1 hNR ⟨X,hX⟩ ⟨C,hFchannel hC⟩

theorem continuous_game_inf (N R : KrausChannel n m) (c δ : ℝ) (hc : 0≤c) (hδ : 0<δ) (hδ1 : δ≤1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap))
    (F : Set (Matrix (Fin n×Fin m) (Fin n×Fin m) ℂ)) (hFcompact : IsCompact F)
    (hFchannel : F⊆channelChoiSet n m) :
    Continuous (fun ρ : densitySet n => ⨅ C : F, game N R δ ρ.val C.val) := by
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hFcompact
  have hto : Continuous (fun z : densitySet n×F => (z.1,(⟨z.2.val,hFchannel z.2.property⟩ : channelChoiSet n m))) :=
    continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hcont := (continuous_game N R c δ hc hδ hδ1 hNR).comp hto
  have hcont' : Continuous (fun z : densitySet n×F => game N R δ z.1.val z.2.val) := by
    simpa only [Function.comp_def] using hcont
  have h := (isCompact_univ : IsCompact (Set.univ : Set F)).continuous_sInf
    (f:=fun (ρ : densitySet n) (C : F) => game N R δ ρ.val C.val) hcont' 
  simpa only [Set.image_univ,iInf] using h

end GeneralizedChannelStein.CanonicalRegularization
