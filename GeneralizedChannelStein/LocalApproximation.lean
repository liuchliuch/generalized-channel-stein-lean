import GeneralizedChannelStein.HaarReconstruction
import GeneralizedChannelStein.WeightedApproximationError
import GeneralizedChannelStein.DimensionDomination
import GeneralizedChannelStein.Lemma27Parameters

/-! # Actual weighted local approximation of permutation-invariant contractions -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein
open QuantumChannelStein Matrix TensorPower TensorPermutation MeasureTheory LocalExpansion
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Quantitative core with a concrete Haar density eliminated from the premises. -/
theorem local_approximation_core {d : ℕ} (hd : 0<d) (τ : State d) (t u h : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hu : 0≤u) (hu1 : u<1) (hh : 0≤h)
    (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (m k R : ℕ) (hm : h≤(m:ℝ)*(t*u^2/2))
    (hR : Real.exp 2*(k:ℝ)*u+2*h≤(R:ℝ))
    (W : Matrix (Index (Fin d) (k+m)) (Index (Fin d) (k+m)) ℂ)
    (hW : W∈invariantAlgebra (Fin d) (k+m)) (hWn : ‖W‖≤1) :
    let v : ℝ := ((k+m+d^2-1).choose (d^2-1) : ℕ)
    ∃ E : Expansion (Fin d) k, E.HasSize R ∧ E.cost≤v*Real.exp ((k:ℝ)*u) ∧
      ‖E.value-weightedExpectation τ k m W‖≤v*Real.exp (-h) := by
  letI : NeZero d := ⟨hd.ne'⟩
  dsimp only
  obtain ⟨f,hf,hfv,hrep⟩ := InvariantIntegral.invariant_integral_representation d (k+m) hd W hW hWn
  obtain ⟨E,hs,hc,he⟩ := exists_local_expansion_of_density τ t u h _
    ht ht1 hu hu1 hh (InvariantOrbitDimension.binomial_mass_real_pos d (k+m))
    hτ f hf hfv m k R hm hR
  refine ⟨E,hs,hc,?_⟩
  have hfi := InvariantIntegral.integrable_weighted d (k+m) f hf
  have hi := weightedExpectation_integral (InvariantIntegral.haar d) τ k m
    (fun U : InvariantIntegral.UnitaryGroup d => U.val) f hfi
  change weightedExpectation τ k m (InvariantIntegral.weightedIntegral d (k+m) f) = _ at hi
  rw [hrep] at hi
  rw [hi]
  exact he

theorem invariant_cast {d n n' : ℕ} (h : n=n')
    (W : Matrix (Index (Fin d) n) (Index (Fin d) n) ℂ)
    (hW : W∈invariantAlgebra (Fin d) n) : (h ▸ W)∈invariantAlgebra (Fin d) n' := by
  subst n'
  exact hW

theorem norm_tensor_cast {d n n' : ℕ} (h : n=n')
    (W : Matrix (Index (Fin d) n) (Index (Fin d) n) ℂ) : ‖(h ▸ W)‖=‖W‖ := by
  subst n'
  rfl

/-- Literal Lemma 27 parameters, retaining the active-regime hypothesis. -/
theorem lemma_27_of_lowerBound {d : ℕ} (hd : 0<d) (τ : State d) (t : ℝ)
    (ht : 0<t) (ht1 : t≤1) (hτ : (τ.matrix-t • (1:Operator d)).PosSemidef)
    (n : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ≤1/16)
    (hn : WeightedDiscardingScalars.blockThreshold d t≤n)
    (hma : (WeightedDiscardingScalars.discardCount n ξ : ℝ)≤(n:ℝ)/2)
    (W : Matrix (Index (Fin d) n) (Index (Fin d) n) ℂ)
    (hW : W∈invariantAlgebra (Fin d) n) (hWn : ‖W‖≤1) :
    ∃ E : Expansion (Fin d) (Lemma27Parameters.k n ξ),
      (∀ i, ((E.sites i).card:ℝ)≤WeightedDiscardingScalars.supportConstant d t*(n:ℝ)^(2/3:ℝ)) ∧
      E.cost≤Real.exp (WeightedDiscardingScalars.supportConstant d t*(n:ℝ)^(2/3:ℝ)) ∧
      ‖E.value-weightedExpectationSplit τ (Lemma27Parameters.k n ξ) (Lemma27Parameters.m n ξ)
        (Lemma27Parameters.paper_parameters ht hξ hξ1 hn hma).split W‖≤ξ := by
  let hp := Lemma27Parameters.paper_parameters ht hξ hξ1 hn hma
  let W' : Matrix (Index (Fin d) (Lemma27Parameters.k n ξ+Lemma27Parameters.m n ξ))
      (Index (Fin d) (Lemma27Parameters.k n ξ+Lemma27Parameters.m n ξ)) ℂ := hp.split.symm ▸ W
  have hW' := invariant_cast hp.split.symm W hW
  have hn' : ‖W'‖≤1 := by rw [show ‖W'‖=‖W‖ from norm_tensor_cast hp.split.symm W]; exact hWn
  obtain ⟨E,hs,hc,he⟩ := local_approximation_core hd τ t (Lemma27Parameters.u d t ξ n)
    (Lemma27Parameters.h d ξ n) ht ht1 hp.u_nonneg hp.u_lt_one hp.h_nonneg hτ
    (Lemma27Parameters.m n ξ) (Lemma27Parameters.k n ξ) (Lemma27Parameters.R d t ξ n)
    hp.cancellation.le hp.cutoff W' hW' hn'
  simp only [hp.split] at hc he
  have hvb := InvariantOrbitDimension.binomial_mass_real_le_polynomial d n
  have hexp : ((d^2-1:ℕ):ℝ)=(d:ℝ)^2-1 := by
    rw [Nat.cast_sub (show 1≤d^2 by nlinarith),Nat.cast_pow,Nat.cast_one]
  rw [← Real.rpow_natCast,hexp] at hvb
  refine ⟨E,?_,?_,?_⟩
  · intro i
    exact (show ((E.sites i).card:ℝ)≤(Lemma27Parameters.R d t ξ n:ℝ) by exact_mod_cast hs i).trans hp.support_bound
  · exact hc.trans (hp.mass_bound _ hvb)
  · exact he.trans (hp.error_bound _ (Nat.cast_nonneg _) hvb)

/-- Faithfulness supplies the actual minimum eigenvalue used in the paper's constants. -/
theorem lemma_27 {d : ℕ} (hd : 0<d) (τ : State d) (hτ : τ.matrix.PosDef)
    (n : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ≤1/16)
    (hn : WeightedDiscardingScalars.blockThreshold d (DimensionDomination.minEigenvalue τ hd)≤n)
    (hma : (WeightedDiscardingScalars.discardCount n ξ : ℝ)≤(n:ℝ)/2)
    (W : Matrix (Index (Fin d) n) (Index (Fin d) n) ℂ)
    (hW : W∈invariantAlgebra (Fin d) n) (hWn : ‖W‖≤1) :
    ∃ E : Expansion (Fin d) (Lemma27Parameters.k n ξ),
      (∀ i, ((E.sites i).card:ℝ)≤WeightedDiscardingScalars.supportConstant d
        (DimensionDomination.minEigenvalue τ hd)*(n:ℝ)^(2/3:ℝ)) ∧
      E.cost≤Real.exp (WeightedDiscardingScalars.supportConstant d
        (DimensionDomination.minEigenvalue τ hd)*(n:ℝ)^(2/3:ℝ)) ∧
      ‖E.value-weightedExpectationSplit τ (Lemma27Parameters.k n ξ) (Lemma27Parameters.m n ξ)
        (Lemma27Parameters.paper_parameters (DimensionDomination.minEigenvalue_pos τ hd hτ) hξ hξ1 hn hma).split W‖≤ξ :=
  lemma_27_of_lowerBound hd τ _ (DimensionDomination.minEigenvalue_pos τ hd hτ)
    (DimensionDomination.minEigenvalue_le_one τ hd)
    (DimensionDomination.scalar_le_of_eigenvalue_lower τ _ (DimensionDomination.minEigenvalue_le τ hd))
    n ξ hξ hξ1 hn hma W hW hWn

end GeneralizedChannelStein
