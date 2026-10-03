import GeneralizedChannelStein.PinchedLikelihood
import GeneralizedChannelStein.SymmetricOutputSpectrum
import GeneralizedChannelStein.CanonicalAttainment
import GeneralizedChannelStein.CommonDominator

/-! # Uniform large-error bound for each symmetric free alternative -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.SymmetricLargeError
open QuantumChannelStein Matrix ChannelEntropy RelativeEntropy TensorChannelCovariance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- Exact map mixtures preserve actual finite-group covariance. -/
theorem covariant_half_mixture {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (p : G →* Equiv.Perm (Fin a)) (q : G →* Equiv.Perm (Fin b))
    (M T U : KrausChannel a b)
    (hM : CovariantOrbitRecovery.Covariant p q M)
    (hT : CovariantOrbitRecovery.Covariant p q T)
    (hU : U.toLinearMap = (1/2:ℂ) • M.toLinearMap + (1/2:ℂ) • T.toLinearMap) :
    CovariantOrbitRecovery.Covariant p q U := by
  have happ (X : Operator a) : U.apply X = (1/2:ℂ) • M.apply X + (1/2:ℂ) • T.apply X :=
    congrArg (fun f : MatrixMap a b => f X) hU
  intro g X
  rw [happ, hM g X, hT g X, happ]
  ext i j
  simp [Matrix.reindex_apply]

/-- The complete bound holds uniformly for every free correlated covariant alternative. -/
theorem singleBeta_le (N : KrausChannel a b) (ha : 0<a) (hb : 0<b)
    (F : AlternativeFamily a b) (hF : Admissible F)
    (ω : State b) (hω : ω.matrix.PosDef)
    (hOne : ((ReplacerChannel.channel a ω).tensorPower 1).toLinearMap ∈ F 1)
    (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (M : KrausChannel (a^n) (b^n)) (hM : M.toLinearMap ∈ F n)
    (hMcov : CovariantOrbitRecovery.Covariant (channelPermutation a n) (channelPermutation b n) M) :
    singleBeta (N.tensorPower n) M ε ≤ ENNReal.ofReal (2 * (2:ℝ) ^
      (-(((familyEntropy (N.tensorPower n) (F n)).toReal -
        Real.logb 2 (((n+(a*b)^2-1).choose ((a*b)^2-1) : ℕ) : ℝ) -
        (1-ε)*((n:ℝ)*replacerRate ω hb+1))/ε))) := by
  let R := (ReplacerChannel.channel a ω).tensorPower n
  have hR : R.toLinearMap ∈ F n := replacer_power_mem F hF.tensor_closed ω hOne n hn
  obtain ⟨U,hU,hmix,hMU,hRU⟩ := exists_common_dominator (F n) (hF.convex n hn) M R hM hR
  let C := replacerRate ω hb
  let L := (n:ℝ)*C+1
  let v : ℝ := ((n+(a*b)^2-1).choose ((a*b)^2-1) : ℕ)
  let E := (familyEntropy (N.tensorPower n) (F n)).toReal
  have hdomR : MatrixMap.CPLe (N.tensorPower n).toLinearMap
      (Complex.ofReal ((2:ℝ)^((n:ℝ)*C)) • R.toLinearMap) :=
    DimensionDomination.faithful_replacer_domination N ω hb hω n
  have heq : 2*(2:ℝ)^((n:ℝ)*C) = (2:ℝ)^L := by
    dsimp [L]
    rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
  have hdom : MatrixMap.CPLe (N.tensorPower n).toLinearMap (Complex.ofReal ((2:ℝ)^L) • U.toLinearMap) := by
    rw [← heq]
    exact cpLe_through_double _ _ _ _ (Real.rpow_nonneg (by norm_num) _) hdomR hRU
  have hUcov := covariant_half_mixture _ _ M R U hMcov
    (tensorPower_covariant (ReplacerChannel.channel a ω) n) hmix
  obtain ⟨ρ,hρ,hmax⟩ := CanonicalAttainment.exists_invariant_maximizer_of_cpLe
    (channelPermutation a n) (channelPermutation b n) (N.tensorPower n) U
    (tensorPower_covariant N n) hUcov ((2:ℝ)^L) (Real.rpow_nonneg (by norm_num) _) hdom (pow_pos ha n)
  let ρ₁ := CanonicalInput.output (N.tensorPower n) ρ
  let σ := CanonicalInput.output U ρ
  let σ₀ := CanonicalInput.output M ρ
  have hdp : (((2:ℝ)^L) • σ.matrix - ρ₁.matrix).PosSemidef :=
    pureOutput_domination _ _ _ hdom (CanonicalInput.input ρ)
  have hd₀ : ((2:ℝ) • σ.matrix - σ₀.matrix).PosSemidef :=
    pureOutput_domination _ _ 2 hMU (CanonicalInput.input ρ)
  have hfinite := admissible_values_finite N ha hb F hF n hn ε hε hε1
  have hEc : (E : EReal) = familyEntropy (N.tensorPower n) (F n) := EReal.coe_toReal hfinite.1 hfinite.2.1
  have hE : E ≤ traceFormula ρ₁ σ := by
    apply EReal.coe_le_coe_iff.mp
    rw [hEc, ← umegaki_of_supportIncluded ρ₁ σ
      (SupportDomination.ker_le_of_posSemidef_smul_sub ρ₁.positive hdp)]
    change familyEntropy (N.tensorPower n) (F n) ≤ CanonicalInput.value (N.tensorPower n) U ρ
    rw [hmax]
    exact familyEntropy_le _ U _ hU
  have hEL : E-Real.logb 2 v < L := by
    have hbnd := (lemma_4 N ha hb F hF ω hω hOne n hn ε hε hε1).1.2
    rw [← hEc, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hbnd
    have hv : 1 ≤ v := by
      dsimp only [v]
      exact_mod_cast InvariantOrbitDimension.binomial_mass_pos (a*b) n
    have hlog : 0 ≤ Real.logb 2 v := Real.logb_nonneg (by norm_num) hv
    dsimp [L,C,E] at *
    linarith
  have hcount : (Fintype.card (SpectralPinching.Block σ) : ℝ) ≤ v := by
    dsimp only [σ,v]
    exact_mod_cast SymmetricOutputSpectrum.canonical_block_card_le ha hb n U hUcov ρ hρ
  obtain ⟨Q,hQ,hcost⟩ := PinchedLikelihood.exists_large_error_effect ρ₁ σ σ₀ E L ε v
    hε hε1 hEL hcount hdp hd₀ hE
  exact (iInf_le (fun t : {t : UnitPureInput (a^n) (a^n) × Effect (a^n*b^n) //
      1-ε ≤ t.2.probability (pureOutput (N.tensorPower n) t.1)} =>
      ENNReal.ofReal (t.val.2.probability (pureOutput M t.val.1)))
      ⟨(CanonicalInput.input ρ,Q),hQ⟩).trans (ENNReal.ofReal_le_ofReal hcost)

end GeneralizedChannelStein.SymmetricLargeError
