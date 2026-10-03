import GeneralizedChannelStein.OperationalMinimax
import GeneralizedChannelStein.UniformAuxiliary
import QuantumChannelStein.BinaryDataProcessing

/-! # Uniform finite-block testing bounds and weak converse

Every intermediate domination hypothesis is explicit. The faithful dimension
bound that instantiates it is a separate concrete matrix theorem.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy OperationalTesting BinaryMeasurement
  BinaryEntropyBounds RelativeEntropy DiamondTesting
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- Every feasible tester must accept a fixed free CP dominator sufficiently often. -/
theorem compositeBeta_lower_of_domination (N M : KrausChannel a b)
    (F : Set (MatrixMap a b)) (hM : M.toLinearMap ∈ F)
    (c : ℝ) (hc : 0 < c) (hdom : MatrixMap.CPLe N.toLinearMap ((c:ℂ) • M.toLinearMap))
    (ε : ℝ) : ENNReal.ofReal ((1-ε)/c) ≤ compositeBeta N F ε := by
  rw [compositeBeta_eq_pure]
  apply le_iInf
  intro t
  have hpq := testValue_le_of_cpLe N.toLinearMap M c hdom t.val.1 t.val.2
  rw [testValue_channel] at hpq
  have hq : (1-ε)/c ≤ t.val.2.probability (pureOutput M t.val.1) :=
    (div_le_iff₀ hc).mpr (by nlinarith [t.property])
  exact (ENNReal.ofReal_le_ofReal hq).trans (le_iSup_of_le ⟨M,hM⟩ le_rfl)

/-- One free domination witness bounds optimized entropy without changing quantifier order. -/
theorem familyEntropy_upper_of_domination (N M : KrausChannel a b)
    (F : Set (MatrixMap a b)) (hM : M.toLinearMap ∈ F)
    (c : ℝ) (hc : 1 ≤ c) (hdom : MatrixMap.CPLe N.toLinearMap ((c:ℂ) • M.toLinearMap)) :
    familyEntropy N F ≤ (Real.logb 2 c : EReal) :=
  (familyEntropy_le N M F hM).trans (channelD_le_log2_of_cpLe N M c hc hdom)

/-- Strictly positive type-II value follows from a free finite dominator. -/
theorem compositeBeta_pos_of_domination (N M : KrausChannel a b)
    (F : Set (MatrixMap a b)) (hM : M.toLinearMap ∈ F)
    (c : ℝ) (hc : 0 < c) (hdom : MatrixMap.CPLe N.toLinearMap ((c:ℂ) • M.toLinearMap))
    (ε : ℝ) (hε : ε < 1) : 0 < compositeBeta N F ε :=
  (ENNReal.ofReal_pos.mpr (div_pos (sub_pos.mpr hε) hc)).trans_le
    (compositeBeta_lower_of_domination N M F hM c hc hdom ε)

/-- A finite state relative entropy forces a positive alternative probability
whenever target acceptance is positive; singular states are included. -/
theorem effect_alternative_pos_of_finite {d : ℕ} (T : Effect d) (ρ σ : State d)
    (hp : 0 < T.probability ρ) (hfinite : umegaki ρ σ < ⊤) :
    0 < T.probability σ := by
  obtain ⟨c,hc,hdom⟩ := (umegaki_lt_top_iff_exists_domination ρ σ).mp hfinite
  have h := probability_le_of_domination T ρ σ c hdom
  by_contra hn
  have hz : T.probability σ = 0 := le_antisymm (le_of_not_gt hn) (T.probability_nonneg σ)
  rw [hz,mul_zero] at h
  exact (not_le_of_gt hp) h

/-- The one-bit binary-entropy bound with an arbitrary upper bound on alternative acceptance. -/
theorem effect_weak_converse {d : ℕ} (T : Effect d) (ρ σ : State d)
    (ε B : ℝ) (hε : ε < 1) (hB : 0 < B) (hB1 : B ≤ 1)
    (hp : 1-ε ≤ T.probability ρ) (hqB : T.probability σ ≤ B) :
    (((1-ε)*(-Real.logb 2 B)-1 : ℝ) : EReal) ≤ umegaki ρ σ := by
  by_cases htop : umegaki ρ σ = ⊤
  · rw [htop]; exact le_top
  have hq0 := effect_alternative_pos_of_finite T ρ σ (by linarith)
    (lt_top_iff_ne_top.mpr htop)
  have hlogB : Real.logb 2 B ≤ 0 := (Real.logb_nonpos_iff (by norm_num) hB).mpr hB1
  have hlogq : Real.logb 2 (T.probability σ) ≤ Real.logb 2 B :=
    (Real.logb_le_logb (by norm_num) hq0 hB).mpr hqB
  have hscalar : (1-ε)*(-Real.logb 2 B)-1 ≤
      binaryRelativeEntropy (T.probability ρ) (T.probability σ) := by
    have hc : Real.logb 2 (1-T.probability σ) ≤ 0 :=
      (Real.logb_nonpos_iff' (by norm_num) (sub_nonneg.mpr (T.probability_le_one σ))).mpr
        (by linarith [T.probability_nonneg σ])
    have hcterm : 0 ≤ -(1-T.probability ρ)*Real.logb 2 (1-T.probability σ) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith [T.probability_le_one ρ]) hc
    have h1 := mul_le_mul_of_nonneg_left hlogq (T.probability_nonneg ρ)
    have h2 := mul_le_mul_of_nonneg_right hp (neg_nonneg.mpr hlogB)
    rw [binaryRelativeEntropy_eq_entropy]
    linarith [binaryEntropyBits_le_one (T.probability ρ)]
  exact (EReal.coe_le_coe_iff.mpr hscalar).trans (binary_measurement_data_processing T ρ σ)

/-- Lemma 4's weak converse before finite entropy is converted to a real number. -/
theorem composite_weak_converse_extended (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hβ : 0 < compositeBeta N F ε) :
    (((1-ε)*(-Real.logb 2 (compositeBeta N F ε).toReal)-1 : ℝ) : EReal) ≤
      familyEntropy N F := by
  have hbnd := compositeBeta_le_one_sub N ha F ε hε hε1.le
  have htop : compositeBeta N F ε ≠ ⊤ :=
    ne_of_lt (hbnd.trans_lt ENNReal.ofReal_lt_top)
  have hB : 0 < (compositeBeta N F ε).toReal := ENNReal.toReal_pos hβ.ne' htop
  have hB1 : (compositeBeta N F ε).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_of_le_ofReal (by linarith : 0 ≤ 1-ε) hbnd).trans (by linarith)
  obtain ⟨ψ,T,hp,heq⟩ := lemma_5_optimal_tester N ha F ε hε
  apply le_iInf
  intro M
  apply le_trans _ (umegaki_pureOutput_le_channelD N M.val ψ)
  apply effect_weak_converse T (pureOutput N ψ) (pureOutput M.val ψ)
    ε (compositeBeta N F ε).toReal hε1 hB hB1 hp
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
  rw [heq]
  exact le_iSup_of_le M le_rfl

/-- A finite free dominator makes both quantities real and gives the displayed
one-bit weak converse; no totalized infinity is used. -/
theorem composite_weak_converse (N M : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (hM : M.toLinearMap ∈ F)
    (c : ℝ) (hc : 1 ≤ c) (hdom : MatrixMap.CPLe N.toLinearMap ((c:ℂ) • M.toLinearMap))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1) :
    (1-ε)*(-Real.logb 2 (compositeBeta N F ε).toReal) ≤
      (familyEntropy N F).toReal + 1 := by
  have hβ := compositeBeta_pos_of_domination N M F hM c (by linarith) hdom ε hε1
  have h := composite_weak_converse_extended N ha F ε hε hε1 hβ
  have hetop : familyEntropy N F ≠ ⊤ :=
    ne_of_lt ((familyEntropy_upper_of_domination N M F hM c hc hdom).trans_lt
      (EReal.coe_lt_top _))
  have hebot : familyEntropy N F ≠ ⊥ :=
    ne_of_gt (EReal.bot_lt_zero.trans_le (familyEntropy_nonneg N ha F))
  rw [← EReal.coe_toReal hetop hebot] at h
  have hr := EReal.coe_le_coe_iff.mp h
  linarith

end GeneralizedChannelStein
