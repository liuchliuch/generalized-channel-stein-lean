import GeneralizedChannelStein.ApproximationConverse
import GeneralizedChannelStein.LemmaFour

/-! # Literal lower testing rate, its bounds, and low-rate block extraction -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein ChannelEntropy DiamondNorm DimensionDomination ParallelExponent Filter
open scoped Topology ComplexOrder MatrixOrder
variable {a b : ℕ}

/-- The proof starts with a liminf, without assuming convergence or identifying entropy. -/
def lowerTestingRate (N : KrausChannel a b) (F : AlternativeFamily a b) (ε : ℝ) : EReal :=
  liminf (compositeExponent N F ε) atTop

theorem compositeExponent_nonneg (N : KrausChannel a b) (ha : 0 < a)
    (F : AlternativeFamily a b) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (n : ℕ) :
    0 ≤ compositeExponent N F ε n := by
  have hb := compositeBeta_le_one_sub (N.tensorPower n) (pow_pos ha n) (F n) ε hε hε1
  have hb1 : compositeBeta (N.tensorPower n) (F n) ε ≤ 1 :=
    hb.trans (ENNReal.ofReal_le_one.mpr (by linarith))
  simpa only [testingExponent_one] using testingExponent_antitone n hb1

theorem lowerTestingRate_nonneg (N : KrausChannel a b) (ha : 0 < a)
    (F : AlternativeFamily a b) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    0 ≤ lowerTestingRate N F ε :=
  le_liminf_of_le (by isBoundedDefault)
    (Eventually.of_forall (compositeExponent_nonneg N ha F ε hε hε1))

/-- The faithful replacer initializes exponential approximation, with zero error. -/
theorem exponentialFreeApprox_replacer (N : KrausChannel a b) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1) :
    ExponentialFreeApprox N F (replacerRate ω hb) := by
  refine ⟨1,1,by norm_num,by norm_num,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  refine ⟨N.tensorPower n,(ReplacerChannel.channel a ω).tensorPower n,
    replacer_power_mem F hF.tensor_closed ω hOne n hn,
    faithful_replacer_domination N ω hb hω n,?_⟩
  rw [sub_self]
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  change ENNReal.ofReal (TraceNorm.traceNorm (0 : Matrix (Fin r × Fin (b^n)) (Fin r × Fin (b^n)) ℂ)) ≤ _
  simp [TraceNorm.traceNorm_zero]

/-- The liminf is finite and bounded by exactly the paper's replacer constant. -/
theorem lowerTestingRate_le_replacer (N : KrausChannel a b) (hb : 0 < b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (ε : ℝ) (hε1 : ε < 1) : lowerTestingRate N F ε ≤ (replacerRate ω hb : EReal) :=
  (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)).trans
    (limsup_exponent_le_approximation_rate N F _
      (exponentialFreeApprox_replacer N hb F hF ω hω hOne) ε hε1)

/-- Every strict margin above the liminf has arbitrarily large good blocks.
This is enough for Proposition 9; convergence of the testing exponent is not assumed. -/
theorem low_rate_subsequence (N : KrausChannel a b) (F : AlternativeFamily a b)
    (ε r : ℝ) (hr : lowerTestingRate N F ε < (r:EReal)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ j, 0 < k j ∧ compositeExponent N F ε (k j) < (r:EReal) := by
  have hfreq := frequently_lt_of_liminf_lt (u := compositeExponent N F ε)
    (by isBoundedDefault) hr
  have hfreq' : ∃ᶠ n : ℕ in atTop, 0 < n ∧ compositeExponent N F ε n < (r:EReal) :=
    hfreq.and_eventually (eventually_gt_atTop (0:ℕ)) |>.mono (fun _ h => ⟨h.2,h.1⟩)
  exact extraction_of_frequently_atTop hfreq'

end GeneralizedChannelStein
