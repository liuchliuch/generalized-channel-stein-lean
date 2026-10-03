import GeneralizedChannelStein.LemmaFour
import GeneralizedChannelStein.UniformAuxiliary

/-! # The rough common-input approximation used in Proposition 9

The hardest alternative is selected using proved composite minimax. Its
auxiliary approximation is uniform over all inputs, with squared error at most
1-epsilon; it is not a pointwise, alternative-dependent tester substitution.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy TestingPrimal UniformAuxiliary Matrix
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder
variable {a b e f : ℕ}

/-- The fixed-error constraint gives the precise hockey-stick margin epsilon/beta. -/
theorem hockeyStick_of_singleBeta (N M : KrausChannel a b) (ha : 0 < a)
    (ε β : ℝ) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hb : ENNReal.ofReal β ≤ singleBeta N M ε) :
    channelHockeyStick N M (ε/β) ≤ 1-ε := by
  obtain ⟨ψ,T,hmax⟩ := exists_pure_maximizer N M ha (ε/β)
  rw [← hmax]
  by_cases hp : 1-ε ≤ T.probability (pureOutput N ψ)
  · have hq : β ≤ T.probability (pureOutput M ψ) := by
      have h := hb.trans (iInf_le (fun t : {t : UnitPureInput a a × Effect (a*b) //
        1-ε ≤ t.2.probability (pureOutput N t.1)} =>
        ENNReal.ofReal (t.val.2.probability (pureOutput M t.val.1))) ⟨(ψ,T),hp⟩)
      exact (ENNReal.ofReal_le_ofReal_iff (T.probability_nonneg _)).mp h
    have hprod : ε ≤ (ε/β)*T.probability (pureOutput M ψ) := by
      calc
        ε = (ε/β)*β := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hq (div_nonneg hε hβ.le)
    dsimp [pureScore]
    linarith [T.probability_le_one (pureOutput N ψ)]
  · have hq : 0 ≤ (ε/β)*T.probability (pureOutput M ψ) :=
      mul_nonneg (div_nonneg hε hβ.le) (T.probability_nonneg _)
    dsimp [pureScore]
    linarith

/-- One hardest free channel yields the same rough margin for every prescribed dilation. -/
theorem exists_rough_free_alternative (N : KrausChannel a b) (ha : 0 < a)
    (F : Set (MatrixMap a b)) (hF : ∀ M ∈ F, IsChannel M)
    (hc : IsCompact (MatrixMap.choi '' F)) (hv : Convex ℝ (MatrixMap.choi '' F))
    (hne : F.Nonempty) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hβ : 0 < compositeBeta N F ε) :
    ∃ M : KrausChannel a b, M.toLinearMap ∈ F ∧
      channelHockeyStick N M (ε/(compositeBeta N F ε).toReal) ≤ 1-ε := by
  obtain ⟨M,hM,hMβ⟩ := lemma_5_hardest N ha F hF hc hv hne ε hε
  have hbnd := compositeBeta_le_one_sub N ha F ε hε hε1.le
  have htop : compositeBeta N F ε ≠ ⊤ := ne_of_lt (hbnd.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨M,hM,hockeyStick_of_singleBeta N M ha ε _ hε
    (ENNReal.toReal_pos hβ.ne' htop) ?_⟩
  rw [ENNReal.ofReal_toReal htop,hMβ]

/-- Actual auxiliary matrix after selecting the hardest alternative, squared error≤1−epsilon. -/
theorem rough_auxiliary_map (N M : KrausChannel a b) (ha : 0 < a)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ)
    (W : Matrix (Fin b × Fin f) (Fin a) ℂ)
    (hV : dilationMap V = N.toLinearMap) (hW : dilationMap W = M.toLinearMap)
    (ε β : ℝ) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hb : ENNReal.ofReal β ≤ singleBeta N M ε) :
    ∃ A : Matrix (Fin e) (Fin f) ℂ,
      ‖A‖ ≤ Real.sqrt (ε/β) ∧
      ‖V-((1:Operator b) ⊗ₖ A)*W‖^2 ≤ 1-ε := by
  obtain ⟨A,hA,he⟩ := lemma_6_testing N M ha V W hV hW (ε/β) (div_nonneg hε hβ.le)
  exact ⟨A,hA,he.trans (hockeyStick_of_singleBeta N M ha ε β hε hβ hb)⟩

end GeneralizedChannelStein
