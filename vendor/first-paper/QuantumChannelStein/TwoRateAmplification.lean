import QuantumChannelStein.TwoRateConstruction
import QuantumChannelStein.TwoRateScalars

/-!
# Two-rate stretched-exponential amplification

Lemma 4.4 is proved using actual auxiliary matrices, natural square-root
blocking, exact remainder padding, and a finite rate iteration. A Chernoff
estimate replaces the paper's entropy-counting tail bound without changing
its statement or assumptions.
-/
noncomputable section
namespace QuantumChannelStein.TwoRateAmplification
open scoped Kronecker Matrix.Norms.L2Operator Topology
open Matrix TensorPower EnvironmentTensor UniformApproximation TwoRateConstruction Filter

variable {a b e f : Type*}
  [Fintype a] [Fintype b] [Fintype e] [Fintype f]
  [DecidableEq a] [DecidableEq b] [DecidableEq e] [DecidableEq f]

omit [DecidableEq e] in
/-- Rate relaxation preserves the actual stretched-exponential approximation. -/
theorem stretched_mono (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ)
    {S R : ℝ} (hSR : S ≤ R) (h : StretchedAtRate U V S) : StretchedAtRate U V R := by
  obtain ⟨K,γ,α,hK,hγ,hα,hα1,happrox⟩ := h
  refine ⟨K,γ,α,hK,hγ,hα,hα1,?_⟩
  filter_upwards [happrox] with n hn
  exact approxAt_mono U V n hSR le_rfl hn

/-- One physical rate-improvement step. All scalar blocking bounds are discharged
by the preceding proved estimates, not assumed as a rate-improvement oracle. -/
theorem rate_improvement
    (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ) (Dstar : Matrix e f ℂ)
    (L r S S' δ β z κ : ℝ)
    (hU : ‖U‖ ≤ 1) (hexact : U = applyEnvironment V Dstar)
    (hDstar : ‖Dstar‖ ≤ (2 : ℝ) ^ (L / 2))
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hz : 1 ≤ z) (hκ : 0 < κ)
    (htail : ∀ k : ℕ, z ^ (-(β * k)) * (1 + δ + z * ((1 + δ) / 2)) ^ k =
      Real.exp (-κ * k))
    (hweak : ∀ᶠ n : ℕ in atTop, ApproxAt U V n r δ)
    (hrS : r < S) (hgap : r + β * (S - r) < S')
    (hstrong : StretchedAtRate U V S) : StretchedAtRate U V S' := by
  obtain ⟨K,γ,α,hK,hγ,hα,hα1,hstrong⟩ := hstrong
  obtain ⟨K',γ',hK',hγ',herr⟩ :=
    TwoRateScalars.sqrt_block_total_error_bound hK hγ hκ hα hα1
  have hεsmall : ∀ᶠ n : ℕ in atTop,
      K * Real.exp (-γ * (n : ℝ) ^ α) ≤ (1 - δ) / 2 :=
    (TwoRateScalars.stretched_error_tendsto_zero K hγ hα).eventually_le_const (by linarith)
  refine ⟨K',γ',α / 2,hK',hγ',by positivity,by linarith,?_⟩
  filter_upwards [TwoRateScalars.eventually_sqrt_padded_cost_le (L := L) hgap,
    herr, TwoRateScalars.tendsto_nat_sqrt_atTop.eventually hweak,
    TwoRateScalars.tendsto_nat_sqrt_atTop.eventually hstrong,
    TwoRateScalars.tendsto_nat_sqrt_atTop.eventually hεsmall]
    with N hcost htotal hweakN hstrongN hsmallN
  obtain ⟨A,hAnorm,hAerror⟩ := two_rate_padded_block U V Dstar L r S δ
    (K * Real.exp (-γ * (Nat.sqrt N : ℝ) ^ α)) β z
    (Nat.sqrt N) (N / Nat.sqrt N) (N % Nat.sqrt N) hU hexact hDstar
    hweakN hstrongN (by positivity) hδ0 hsmallN hrS.le hz
  rw [htail] at hAerror
  have hresult : ApproxAt U V (Nat.sqrt N * (N / Nat.sqrt N) + N % Nat.sqrt N) S'
      (K' * Real.exp (-γ' * (N : ℝ) ^ (α / 2))) := by
    refine ⟨A, ?_, hAerror.trans htotal⟩
    simpa only [Nat.div_add_mod] using hAnorm.trans hcost
  simpa only [Nat.div_add_mod] using hresult

/-- **Lemma 4.4 (Two-rate tensor amplification).** A uniform weak approximation
strictly below one at rate r, together with a finite-rate exact comparison,
gives stretched-exponential approximation at every rate R>r. -/
theorem lemma_4_4
    (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ) (Dstar : Matrix e f ℂ)
    (L r R δ : ℝ) (hU : Uᴴ * U = 1)
    (hexact : U = applyEnvironment V Dstar) (hDstar : ‖Dstar‖ ≤ (2 : ℝ) ^ (L / 2))
    (_hr0 : 0 ≤ r) (hrL : r < L) (hR : r < R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hweak : ∀ᶠ n : ℕ in atTop, ApproxAt U V n r δ) : StretchedAtRate U V R := by
  obtain ⟨β,z,κ,hβ0,hβ1,hz,hκ,_,htail⟩ :=
    TwoRateScalars.exists_two_rate_tail_parameters hδ0 hδ1
  have hstart := stretched_of_exact U V Dstar L hexact hDstar
  obtain ⟨j,hj,hP⟩ := TwoRateScalars.exists_improved_rate hrL hR hβ0 hβ1 hstart
    (fun S S' hrS hmix hstrong => rate_improvement U V Dstar L r S S' δ β z κ
      (norm_isometry_le_one U hU) hexact hDstar hδ0 hδ1 hz.le hκ htail hweak hrS
      (by nlinarith) hstrong)
  exact stretched_mono U V hj.le hP

omit [DecidableEq e] in
/-- Stretched-exponential approximation is in particular vanishing uniform error. -/
theorem stretched_vanishing (U : Matrix (b × e) a ℂ) (V : Matrix (b × f) a ℂ)
    {S : ℝ} (h : StretchedAtRate U V S) : VanishingAtRate U V S := by
  obtain ⟨K,γ,α,_,hγ,hα,_,happrox⟩ := h
  intro ε hε
  filter_upwards [happrox,
    (TwoRateScalars.stretched_error_tendsto_zero K hγ hα).eventually_le_const hε]
    with n hn he
  exact approxAt_mono U V n le_rfl he hn

end QuantumChannelStein.TwoRateAmplification
