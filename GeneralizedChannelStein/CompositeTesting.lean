import GeneralizedChannelStein.Families
import QuantumChannelStein.IdenticalChannelTesting

/-! # Composite testing with the operational quantifiers preserved

A single feasible tester is chosen before the worst-case free alternative.
Arbitrary finite references and mixed inputs are allowed. The equality with the
pure input-sized-reference normal form preserves every alternative at once.
-/
noncomputable section
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy OperationalTesting
open ParallelTestingReduction IdenticalChannelTesting

variable {a b : ℕ}

/-- Free alternatives as Kraus witnesses of actual map membership. -/
def FreeChannel (F : Set (MatrixMap a b)) := {M : KrausChannel a b // M.toLinearMap ∈ F}

/-- The worst-case alternative is selected after the uniform tester. -/
def worstAcceptance (F : Set (MatrixMap a b)) (t : ChannelTest a b) : ENNReal :=
  ⨆ M : FreeChannel F, ENNReal.ofReal (t.acceptance M.val)

/-- Literal composite operational beta: inf of a supremum, never reversed. -/
def compositeBeta (N : KrausChannel a b) (F : Set (MatrixMap a b)) (ε : ℝ) : ENNReal :=
  ⨅ t : {t : ChannelTest a b // 1-ε ≤ t.acceptance N}, worstAcceptance F t.val

/-- Input-sized pure form of equation (4), with the same quantifier order. -/
def compositePureBeta (N : KrausChannel a b) (F : Set (MatrixMap a b)) (ε : ℝ) : ENNReal :=
  ⨅ t : {t : UnitPureInput a a × Effect (a*b) //
    1-ε ≤ t.2.probability (pureOutput N t.1)},
    ⨆ M : FreeChannel F, ENNReal.ofReal (t.val.2.probability (pureOutput M.val t.val.1))

/-- A fixed alternative has input-optimized Umegaki before the family infimum. -/
def familyEntropy (N : KrausChannel a b) (F : Set (MatrixMap a b)) : EReal :=
  ⨅ M : FreeChannel F, channelD N M.val

/-- Every admissible positive block has actual free Kraus witnesses. -/
theorem freeChannel_nonempty {F : AlternativeFamily a b} (hF : Admissible F)
    (n : ℕ) (hn : 0 < n) : Nonempty (FreeChannel (F n)) := by
  obtain ⟨M,hm⟩ := hF.nonempty n hn
  obtain ⟨K,hK⟩ := (isChannel_iff_kraus M).mp (hF.channels n hn M hm)
  exact ⟨⟨K,hK ▸ hm⟩⟩

/-- Purification/compression preserves the whole family, not merely one alternative. -/
theorem compositeBeta_eq_pure (N : KrausChannel a b)
    (F : Set (MatrixMap a b)) (ε : ℝ) :
    compositeBeta N F ε = compositePureBeta N F ε := by
  apply le_antisymm
  · apply le_iInf
    intro t
    refine iInf_le_of_le ⟨ofPureTest t.val.1 t.val.2, ?_⟩ ?_
    · simpa only [ofPureTest_acceptance] using t.property
    · simp only [worstAcceptance, ofPureTest_acceptance, le_refl]
  · apply le_iInf
    intro t
    obtain ⟨ψ,T,h⟩ := exists_pure_test t.val
    refine iInf_le_of_le ⟨(ψ,T), ?_⟩ ?_
    · rw [h]
      exact t.property
    · simp only [worstAcceptance, h, le_refl]

/-- All worst-case acceptances are probabilities, even for an empty family. -/
theorem worstAcceptance_le_one (F : Set (MatrixMap a b)) (t : ChannelTest a b) :
    worstAcceptance F t ≤ 1 := by
  apply iSup_le
  intro M
  exact ENNReal.ofReal_le_one.mpr (t.acceptance_le_one M.val)

/-- One free member's acceptance is bounded by the worst case. -/
theorem acceptance_le_worst (F : Set (MatrixMap a b)) (t : ChannelTest a b)
    (M : KrausChannel a b) (hM : M.toLinearMap ∈ F) :
    ENNReal.ofReal (t.acceptance M) ≤ worstAcceptance F t :=
  le_iSup (fun K : FreeChannel F => ENNReal.ofReal (t.acceptance K.val)) ⟨M,hM⟩

/-- Enlarging the alternative family can only increase optimal type-II error. -/
theorem compositeBeta_mono_family (N : KrausChannel a b)
    {F G : Set (MatrixMap a b)} (hFG : F ⊆ G) (ε : ℝ) :
    compositeBeta N F ε ≤ compositeBeta N G ε := by
  apply iInf_mono
  intro t
  apply iSup_le
  intro M
  exact acceptance_le_worst G t.val M.val (hFG M.property)

/-- Relaxing type-I tolerance can only lower the optimized type-II error. -/
theorem compositeBeta_antitone_tolerance (N : KrausChannel a b)
    (F : Set (MatrixMap a b)) {ε η : ℝ} (h : ε ≤ η) :
    compositeBeta N F η ≤ compositeBeta N F ε := by
  apply le_iInf
  intro t
  exact iInf_le_of_le ⟨t.val, by linarith [t.property]⟩ le_rfl

/-- Lemma 4's elementary upper bound, for every family without additional axioms. -/
theorem compositeBeta_le_one_sub (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    compositeBeta N F ε ≤ ENNReal.ofReal (1-ε) := by
  rw [compositeBeta_eq_pure]
  let ψ := unitProductInput ha
  let T := coinEffect (a*b) (1-ε) (sub_nonneg.mpr hε1) (by linarith)
  refine iInf_le_of_le ⟨(ψ,T), ?_⟩ ?_
  · simp [T]
  · apply iSup_le
    intro M
    simp [T]

/-- The optimized entropy retains extended values until finiteness is proved. -/
theorem familyEntropy_nonneg (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) : 0 ≤ familyEntropy N F := by
  apply le_iInf
  intro M
  exact channelD_nonneg N M.val ha

/-- Each actual free channel gives an entropy upper bound. -/
theorem familyEntropy_le (N M : KrausChannel a b) (F : Set (MatrixMap a b))
    (hM : M.toLinearMap ∈ F) : familyEntropy N F ≤ channelD N M :=
  iInf_le (fun K : FreeChannel F => channelD N K.val) ⟨M,hM⟩

end GeneralizedChannelStein
