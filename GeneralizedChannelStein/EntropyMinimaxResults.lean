import GeneralizedChannelStein.CanonicalRegularization
import GeneralizedChannelStein.EntropyInfimumGap
import GeneralizedChannelStein.CompositeTesting
import GeneralizedChannelStein.LemmaFour
import QuantumChannelStein.TensorChannelCovariance

/-! Exact unregularized channel-family entropy minimax and attainment. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.EntropyMinimaxResults
open QuantumChannelStein Matrix ChannelEntropy RelativeEntropy CanonicalInput CanonicalAttainment CanonicalRegularization
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
variable {n m : ℕ}
abbrev ChoiSpace (n m : ℕ) := Matrix (Fin n×Fin m) (Fin n×Fin m) ℂ

def alternative (F : Set (ChoiSpace n m)) (hF : F⊆channelChoiSet n m) (C : F) : KrausChannel n m :=
  choiChannel ⟨C.val,hF C.property⟩

theorem alternative_map (F : Set (ChoiSpace n m)) (hF : F⊆channelChoiSet n m) (C : F)
    (M : KrausChannel n m) (hC : C.val=M.choi) : (alternative F hF C).toLinearMap=M.toLinearMap := by
  apply MatrixMap.choi_injective
  simp only [MatrixMap.choi_toLinearMap,alternative,choiChannel_choi]
  exact hC

theorem value_congr_alt (N M M' : KrausChannel n m) (hM : M.toLinearMap=M'.toLinearMap) (ρ : State n) :
    value N M ρ=value N M' ρ := by
  unfold value output
  rw [pureOutput_congr M M' hM]

def inputInf (N : KrausChannel n m) (F : Set (ChoiSpace n m)) (hF : F⊆channelChoiSet n m) (ρ : State n) : EReal :=
  ⨅ C : F, value N (alternative F hF C) ρ

def outerInf (N : KrausChannel n m) (F : Set (ChoiSpace n m)) (hF : F⊆channelChoiSet n m) : EReal :=
  ⨅ C : F, channelD N (alternative F hF C)

theorem inputInf_le_outerInf (N : KrausChannel n m) (F : Set (ChoiSpace n m))
    (hF : F⊆channelChoiSet n m) (ρ : State n) : inputInf N F hF ρ ≤ outerInf N F hF := by
  apply le_iInf
  intro C
  exact (iInf_le _ C).trans (value_le_channelD N _ ρ)

theorem inputInf_bounds (N R : KrausChannel n m) (F : Set (ChoiSpace n m))
    (hF : F⊆channelChoiSet n m) (hR : R.choi∈F) (c : ℝ) (hc : 1 ≤ c)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (ρ : State n) :
    0 ≤ inputInf N F hF ρ ∧ inputInf N F hF ρ ≤ (Real.logb 2 c:EReal) := by
  constructor
  · exact le_iInf fun C => value_nonneg N _ ρ
  · have h := iInf_le (fun C : F => value N (alternative F hF C) ρ) ⟨R.choi,hR⟩
    rw [value_congr_alt N _ R (alternative_map F hF ⟨R.choi,hR⟩ R rfl)] at h
    exact h.trans (pureOutput_umegaki_le N R c hc hNR (input ρ))

theorem outerInf_bounds (N R : KrausChannel n m) (F : Set (ChoiSpace n m))
    (hF : F⊆channelChoiSet n m) (hR : R.choi∈F) (c : ℝ) (hc : 1 ≤ c)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (hn : 0<n) :
    0 ≤ outerInf N F hF ∧ outerInf N F hF ≤ (Real.logb 2 c:EReal) := by
  constructor
  · exact le_iInf fun C => channelD_nonneg N _ hn
  · have h := iInf_le (fun C : F => channelD N (alternative F hF C)) ⟨R.choi,hR⟩
    rw [channelD_congr N N _ R rfl (alternative_map F hF ⟨R.choi,hR⟩ R rfl)] at h
    exact h.trans (channelD_le_log2_of_cpLe N R c hc hNR)

def regIndex (R : KrausChannel n m) (F : Set (ChoiSpace n m)) (hconv : Convex ℝ F) (hR : R.choi∈F)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (C : F) : F :=
  ⟨regChoi R δ C.val,hconv C.property hR (sub_nonneg.mpr hδ1) hδ (by ring)⟩

theorem game_eq_regularized_value (N R : KrausChannel n m) (F : Set (ChoiSpace n m))
    (hF : F⊆channelChoiSet n m) (hconv : Convex ℝ F) (hR : R.choi∈F)
    (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0<δ) (hδ1 : δ ≤ 1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (ρ : densitySet n) (C : F) :
    (game N R δ ρ.val C.val:EReal)=value N (alternative F hF (regIndex R F hconv hR δ hδ.le hδ1 C)) (ofDensity ρ) := by
  exact (value_eq_game N R c δ hc hδ hδ1 hNR ρ ⟨C.val,hF C.property⟩).symm

/-- A dimension-dependent linear regularization error follows directly from
proved joint convexity; it suffices for the exact minimax limit. -/
theorem game_le_original_add (N R : KrausChannel n m) (c δ : ℝ) (hc : 1 ≤ c) (hδ : 0<δ) (hδ1 : δ ≤ 1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (ρ : densitySet n) (C : channelChoiSet n m) :
    (game N R δ ρ.val C.val:EReal) ≤ value N (choiChannel C) (ofDensity ρ)+((δ*Real.logb 2 c:ℝ):EReal) := by
  have h := EntropyMinimax.value_convex_alternative_real N (choiChannel C) R (regChannel R δ hδ.le hδ1 C)
    (ofDensity ρ) (1-δ) (sub_nonneg.mpr hδ1) (by linarith) (by simpa using regChannel_map R δ hδ.le hδ1 C)
  rw [sub_sub_cancel,value_eq_game N R c δ (zero_le_one.trans hc) hδ hδ1 hNR] at h
  have hleft : ((1-δ:ℝ):EReal)*value N (choiChannel C) (ofDensity ρ) ≤ value N (choiChannel C) (ofDensity ρ) := by
    have hh := mul_le_mul_of_nonneg_right (show ((1-δ:ℝ):EReal) ≤ 1 by exact_mod_cast (show 1-δ ≤ 1 by linarith))
      (value_nonneg N (choiChannel C) (ofDensity ρ))
    simpa only [one_mul] using hh
  have hRval : value N R (ofDensity ρ) ≤ (Real.logb 2 c:EReal) :=
    pureOutput_umegaki_le N R c hc hNR (input (ofDensity ρ))
  have hright := mul_le_mul_of_nonneg_left hRval (EReal.coe_nonneg.mpr hδ.le)
  rw [← EReal.coe_mul] at hright
  exact h.trans (add_le_add hleft hright)

theorem regularized_input_gap (N R : KrausChannel n m) (F : Set (ChoiSpace n m))
    (hF : F⊆channelChoiSet n m) (hconv : Convex ℝ F) (hR : R.choi∈F)
    (c δ : ℝ) (hc : 1 ≤ c) (hδ : 0<δ) (hδ1 : δ ≤ 1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (ρ : densitySet n) :
    |(⨅ C : F, game N R δ ρ.val C.val)-(inputInf N F hF (ofDensity ρ)).toReal| ≤ δ*Real.logb 2 c := by
  letI : Nonempty F := ⟨⟨R.choi,hR⟩⟩
  have hB : 0 ≤ Real.logb 2 c := Real.logb_nonneg (by norm_num) hc
  have h := EntropyInfimumGap.infimum_gap_of_regularization
    (fun C : F => value N (alternative F hF C) (ofDensity ρ))
    (fun C : F => game N R δ ρ.val C.val) (regIndex R F hconv hR δ hδ.le hδ1)
    (Real.logb 2 c) (δ*Real.logb 2 c)
    (fun C => value_nonneg N _ _) hB
    (by
      refine ⟨⟨R.choi,hR⟩,?_⟩
      dsimp only
      rw [value_congr_alt N _ R (alternative_map F hF ⟨R.choi,hR⟩ R rfl)]
      exact pureOutput_umegaki_le N R c hc hNR (input (ofDensity ρ)))
    (fun C => game_nonneg N R c δ (zero_le_one.trans hc) hδ hδ1 hNR ρ ⟨C.val,hF C.property⟩)
    (mul_nonneg hδ.le hB)
    (fun C => game_eq_regularized_value N R F hF hconv hR c δ (zero_le_one.trans hc) hδ hδ1 hNR ρ C)
    (fun C => game_le_original_add N R c δ hc hδ hδ1 hNR ρ ⟨C.val,hF C.property⟩)
  dsimp only at h
  unfold inputInf
  rw [abs_of_nonneg h.2.2.1]
  exact h.2.2.2

theorem outer_real_le_regularized_sup (N R : KrausChannel n m) (F : Set (ChoiSpace n m))
    (hF : F ⊆ channelChoiSet n m) (hcompact : IsCompact F) (hconv : Convex ℝ F) (hR : R.choi∈F)
    (c δ : ℝ) (hc : 1 ≤ c) (hδ : 0<δ) (hδ1 : δ ≤ 1)
    (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (hn : 0<n) :
    (outerInf N F hF).toReal ≤ ⨆ ρ : densitySet n, ⨅ C : F, game N R δ ρ.val C.val := by
  letI : Nonempty F := ⟨⟨R.choi,hR⟩⟩
  letI : Nonempty (densitySet n) := ⟨toDensity (FaithfulDensity.maximallyMixed n hn)⟩
  have hB := outerInf_bounds N R F hF hR c hc hNR hn
  have hE := EReal.coe_toReal (ne_of_lt (hB.2.trans_lt (EReal.coe_lt_top _)))
    (ne_of_gt (EReal.bot_lt_zero.trans_le hB.1))
  rw [← game_minimax N R c δ hc hδ hδ1 hNR hn F hcompact hconv ⟨R.choi,hR⟩ hF]
  apply le_ciInf
  intro C
  let C' : channelChoiSet n m := ⟨C.val,hF C.property⟩
  let M := regChannel R δ hδ.le hδ1 C'
  have hdom := target_domination N R c δ (zero_le_one.trans hc) hδ hδ1 hNR C'
  obtain ⟨ρ,hρ⟩ := exists_maximizer_of_cpLe N M (c/δ) (div_nonneg (zero_le_one.trans hc) hδ.le) hdom hn
  have hOuter : outerInf N F hF ≤ channelD N M :=
    iInf_le (fun D : F => channelD N (alternative F hF D)) (regIndex R F hconv hR δ hδ.le hδ1 C)
  have hpoint : channelD N M=(game N R δ ρ.matrix C.val:EReal) := by
    rw [← hρ]
    have h := value_eq_game N R c δ (zero_le_one.trans hc) hδ hδ1 hNR (toDensity ρ) C'
    simpa only [ofDensity_toDensity,toDensity] using h
  have hbb : BddAbove (Set.range (fun σ : densitySet n => game N R δ σ.val C.val)) :=
    ⟨Real.logb 2 (c/δ),by rintro y ⟨σ,rfl⟩; exact game_le_log N R c δ hc hδ hδ1 hNR σ C'⟩
  have hgame := le_ciSup hbb (toDensity ρ)
  have hle := hOuter.trans (hpoint.trans_le (EReal.coe_le_coe_iff.mpr hgame))
  rw [← hE] at hle
  exact EReal.coe_le_coe_iff.mp hle

/-- Exact minimax and maximum attainment for an actual compact convex Choi
family containing one uniformly dominating alternative. -/
theorem choi_entropy_minimax (N R : KrausChannel n m) (F : Set (ChoiSpace n m))
    (hF : F ⊆ channelChoiSet n m) (hcompact : IsCompact F) (hconv : Convex ℝ F) (hR : R.choi∈F)
    (c : ℝ) (hc : 1 ≤ c) (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (hn : 0<n) :
    outerInf N F hF=(⨆ ρ : State n, inputInf N F hF ρ) ∧
      ∃ ρ : State n, inputInf N F hF ρ=outerInf N F hF := by
  letI : CompactSpace (densitySet n) := isCompact_iff_compactSpace.mp (isCompact_densitySet n)
  letI : Nonempty (densitySet n) := ⟨toDensity (FaithfulDensity.maximallyMixed n hn)⟩
  let g : densitySet n→ℝ := fun ρ => (inputInf N F hF (ofDensity ρ)).toReal
  let gδ : ℝ→densitySet n→ℝ := fun δ ρ => ⨅ C : F, game N R δ ρ.val C.val
  let E := (outerInf N F hF).toReal
  have hB := outerInf_bounds N R F hF hR c hc hNR hn
  have hE := EReal.coe_toReal (ne_of_lt (hB.2.trans_lt (EReal.coe_lt_top _)))
    (ne_of_gt (EReal.bot_lt_zero.trans_le hB.1))
  have hweak : ∀ ρ : densitySet n, g ρ ≤ E := by
    intro ρ
    have hI := inputInf_bounds N R F hF hR c hc hNR (ofDensity ρ)
    have hρ := EReal.coe_toReal (ne_of_lt (hI.2.trans_lt (EReal.coe_lt_top _)))
      (ne_of_gt (EReal.bot_lt_zero.trans_le hI.1))
    have hh := inputInf_le_outerInf N F hF (ofDensity ρ)
    rw [← hρ,← hE] at hh
    exact EReal.coe_le_coe_iff.mp hh
  obtain ⟨hcont,hsup,ρ,hρ⟩ := EntropyMinimaxLimit.regularized_minimax_attained g gδ E (Real.logb 2 c)
    (Real.logb_nonneg (by norm_num) hc)
    (fun δ hδ hδ1 => continuous_game_inf N R c δ (zero_le_one.trans hc) hδ hδ1.le hNR F hcompact hF)
    (fun δ hδ hδ1 ρ => regularized_input_gap N R F hF hconv hR c δ hc hδ hδ1.le hNR ρ)
    hweak
    (fun δ hδ hδ1 => outer_real_le_regularized_sup N R F hF hcompact hconv hR c δ hc hδ hδ1.le hNR hn)
  have hI := inputInf_bounds N R F hF hR c hc hNR (ofDensity ρ)
  have hρcoe := EReal.coe_toReal (ne_of_lt (hI.2.trans_lt (EReal.coe_lt_top _)))
    (ne_of_gt (EReal.bot_lt_zero.trans_le hI.1))
  have hactual : inputInf N F hF (ofDensity ρ)=outerInf N F hF := by
    rw [← hρcoe,← hE]
    exact congrArg (fun x : ℝ => (x:EReal)) hρ
  refine ⟨le_antisymm ?_ ?_,⟨ofDensity ρ,hactual⟩⟩
  · rw [← hactual]
    exact le_iSup (inputInf N F hF) (ofDensity ρ)
  · exact iSup_le (inputInf_le_outerInf N F hF)

/-- The paper's inner optimization, over all actual free channel maps through
Kraus witnesses; the represented map, not the witness, determines the value. -/
def familyInputValue (N : KrausChannel n m) (F : Set (MatrixMap n m)) (ρ : State n) : EReal :=
  ⨅ M : FreeChannel F, value N M.val ρ

theorem choi_family_channels (F : Set (MatrixMap n m)) (hF : ∀ M∈F, IsChannel M) :
    MatrixMap.choi '' F ⊆ channelChoiSet n m := by
  rintro C ⟨M,hM,rfl⟩
  exact ⟨MatrixMap.choi_positive_of_completelyPositive M (hF M hM).1,
    MatrixMap.traceOutput_choi_of_trace_preserving M (hF M hM).2⟩

theorem outerInf_eq_familyEntropy (N : KrausChannel n m) (F : Set (MatrixMap n m))
    (hF : ∀ M∈F, IsChannel M) :
    outerInf N (MatrixMap.choi '' F) (choi_family_channels F hF)=familyEntropy N F := by
  apply le_antisymm
  · apply le_iInf
    intro M
    let C : MatrixMap.choi '' F := ⟨M.val.choi,M.val.toLinearMap,M.property,MatrixMap.choi_toLinearMap M.val⟩
    have h := iInf_le (fun C : MatrixMap.choi '' F => channelD N (alternative _ (choi_family_channels F hF) C)) C
    exact h.trans_eq (channelD_congr N N _ M.val rfl (alternative_map _ _ C M.val rfl))
  · apply le_iInf
    intro C
    obtain ⟨M,hM,hC⟩ := C.property
    let K := alternative (MatrixMap.choi '' F) (choi_family_channels F hF) C
    have hK : K.toLinearMap=M := by
      apply MatrixMap.choi_injective
      rw [MatrixMap.choi_toLinearMap]
      exact (choiChannel_choi _).trans hC.symm
    have hKmem : K.toLinearMap∈F := hK.symm ▸ hM
    exact iInf_le (fun P : FreeChannel F => channelD N P.val) ⟨K,hKmem⟩

theorem inputInf_eq_familyInput (N : KrausChannel n m) (F : Set (MatrixMap n m))
    (hF : ∀ M∈F, IsChannel M) (ρ : State n) :
    inputInf N (MatrixMap.choi '' F) (choi_family_channels F hF) ρ=familyInputValue N F ρ := by
  apply le_antisymm
  · apply le_iInf
    intro M
    let C : MatrixMap.choi '' F := ⟨M.val.choi,M.val.toLinearMap,M.property,MatrixMap.choi_toLinearMap M.val⟩
    have h := iInf_le (fun C : MatrixMap.choi '' F => value N (alternative _ (choi_family_channels F hF) C) ρ) C
    exact h.trans_eq (value_congr_alt N _ M.val (alternative_map _ _ C M.val rfl) ρ)
  · apply le_iInf
    intro C
    obtain ⟨M,hM,hC⟩ := C.property
    let K := alternative (MatrixMap.choi '' F) (choi_family_channels F hF) C
    have hK : K.toLinearMap=M := by
      apply MatrixMap.choi_injective
      rw [MatrixMap.choi_toLinearMap]
      exact (choiChannel_choi _).trans hC.symm
    have hKmem : K.toLinearMap∈F := hK.symm ▸ hM
    exact iInf_le (fun P : FreeChannel F => value N P.val ρ) ⟨K,hKmem⟩

/-- Intrinsic channel-family version, with no Choi optimization left implicit. -/
theorem family_entropy_minimax (N R : KrausChannel n m) (F : Set (MatrixMap n m))
    (hF : ∀ M∈F, IsChannel M) (hcompact : IsCompact (MatrixMap.choi '' F))
    (hconv : Convex ℝ (MatrixMap.choi '' F)) (hR : R.toLinearMap∈F)
    (c : ℝ) (hc : 1 ≤ c) (hNR : MatrixMap.CPLe N.toLinearMap ((c:ℂ)•R.toLinearMap)) (hn : 0<n) :
    familyEntropy N F=(⨆ ρ : State n, familyInputValue N F ρ) ∧
      ∃ ρ : State n, familyInputValue N F ρ=familyEntropy N F := by
  have hR' : R.choi∈MatrixMap.choi '' F := ⟨R.toLinearMap,hR,MatrixMap.choi_toLinearMap R⟩
  have h := choi_entropy_minimax N R (MatrixMap.choi '' F) (choi_family_channels F hF)
    hcompact hconv hR' c hc hNR hn
  have ho := outerInf_eq_familyEntropy N F hF
  have hi : inputInf N (MatrixMap.choi '' F) (choi_family_channels F hF)=familyInputValue N F :=
    funext (inputInf_eq_familyInput N F hF)
  rw [ho,hi] at h
  exact h

/-- Lemma32's exact entropy minimax equality and maximum attainment under
F1--F3, with no auxiliary continuity, compactness, or closure premise. -/
theorem lemma_32 {a b : ℕ} (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F) (k : ℕ) (hk : 0<k) :
    familyEntropy (N.tensorPower k) (F k)=
      (⨆ ρ : State (a^k), familyInputValue (N.tensorPower k) (F k) ρ) ∧
      ∃ ρ : State (a^k), familyInputValue (N.tensorPower k) (F k) ρ=familyEntropy (N.tensorPower k) (F k) := by
  obtain ⟨ω,hω,hOne⟩ := hF.faithful_replacer
  let R := (ReplacerChannel.channel a ω).tensorPower k
  let c : ℝ := (2:ℝ)^((k:ℝ)*replacerRate ω hb)
  have hR : R.toLinearMap∈F k := replacer_power_mem F hF.tensor_closed ω hOne k hk
  have hdom : MatrixMap.CPLe (N.tensorPower k).toLinearMap ((c:ℂ)•R.toLinearMap) :=
    DimensionDomination.faithful_replacer_domination N ω hb hω k
  have hc : 1 ≤ c := one_le_domination_constant _ _ (N.tensorPower k).trace_apply R.trace_apply
    (PureReferenceRecovery.inputDensity (unitProductInput (pow_pos ha k))) hdom
  exact family_entropy_minimax (N.tensorPower k) R (F k) (hF.channels k hk)
    (hF.compact k hk) (hF.convex k hk) hR c hc hdom (pow_pos ha k)

/-- The symmetric-optimizer clause in the same block setting as the paper.
Its positive component is the actual tensor power of the fixed faithful replacer. -/
theorem lemma_32_symmetric {a b : ℕ} {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (N : KrausChannel a b) (ha : 0<a) (hb : 0<b) (k : ℕ)
    (p : G→*Equiv.Perm (Fin (a^k))) (q : G→*Equiv.Perm (Fin (b^k)))
    (M : KrausChannel (a^k) (b^k))
    (hN : CovariantOrbitRecovery.Covariant p q (N.tensorPower k))
    (hM : CovariantOrbitRecovery.Covariant p q M)
    (ω : State b) (hω : ω.matrix.PosDef) (η : ℝ) (hη : 0<η)
    (hR : MatrixMap.CPLe ((η:ℂ)•((ReplacerChannel.channel a ω).tensorPower k).toLinearMap) M.toLinearMap) :
    ∃ ρ : State (a^k), (∀ g, Matrix.reindex (p g) (p g) ρ.matrix=ρ.matrix) ∧
      value (N.tensorPower k) M ρ=channelD (N.tensorPower k) M := by
  let R := (ReplacerChannel.channel a ω).tensorPower k
  let c : ℝ := (2:ℝ)^((k:ℝ)*replacerRate ω hb)
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hdom := cpLe_of_positive_component (N.tensorPower k) R M c η hc hη
    (DimensionDomination.faithful_replacer_domination N ω hb hω k) hR
  exact exists_invariant_maximizer_of_cpLe p q (N.tensorPower k) M hN hM (c/η)
    (div_nonneg hc hη.le) hdom (pow_pos ha k)

/-- Paper specialization: target permutation covariance is proved for the
actual tensor powers, so only the alternative's covariance is hypothesized. -/
theorem lemma_32_permutation_optimizer {a b : ℕ}
    (N : KrausChannel a b) (ha : 0<a) (hb : 0<b) (k : ℕ)
    (M : KrausChannel (a^k) (b^k))
    (hM : CovariantOrbitRecovery.Covariant (TensorChannelCovariance.channelPermutation a k)
      (TensorChannelCovariance.channelPermutation b k) M)
    (ω : State b) (hω : ω.matrix.PosDef) (η : ℝ) (hη : 0<η)
    (hR : MatrixMap.CPLe ((η:ℂ)•((ReplacerChannel.channel a ω).tensorPower k).toLinearMap) M.toLinearMap) :
    ∃ ρ : State (a^k),
      (∀ π : Equiv.Perm (Fin k), Matrix.reindex (TensorChannelCovariance.channelPermutation a k π)
        (TensorChannelCovariance.channelPermutation a k π) ρ.matrix=ρ.matrix) ∧
      value (N.tensorPower k) M ρ=channelD (N.tensorPower k) M :=
  lemma_32_symmetric N ha hb k (TensorChannelCovariance.channelPermutation a k)
    (TensorChannelCovariance.channelPermutation b k) M (TensorChannelCovariance.tensorPower_covariant N k)
    hM ω hω η hη hR

end GeneralizedChannelStein.EntropyMinimaxResults
