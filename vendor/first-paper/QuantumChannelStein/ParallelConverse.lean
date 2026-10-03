import QuantumChannelStein.ExponentialStinespring
import QuantumChannelStein.OperationalTesting

/-!
# Exponential parallel strong converse and the upper hockey-stick rate

All probabilities below are Born probabilities of the paper's actual
fixed-reference pure tests. The exponential estimate is uniform over their
inputs and effects, and follows from the proved Theorem 2.2 and Proposition 4.2.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.ParallelConverse
open scoped BigOperators Kronecker Matrix.Norms.L2Operator Topology
open Matrix ChannelEntropy TestingPrimal HockeyStickApproximation
  ChannelDilationPower ExponentialStinespring OperationalTesting Filter
variable {a b : ℕ}

/-- The canonical Kraus Stinespring matrix implements the original channel. -/
theorem dilationMap_stinespring (Φ : KrausChannel a b) :
    dilationMap Φ.stinespring = Φ.toLinearMap := by
  ext X i j
  rw [dilationMap_apply, Φ.traceEnvironment_stinespring]
  rfl

/-- The upper-rate half of Corollary 5.1, with a uniform explicit exponential
majorant for the actual optimized channel hockey-stick quantity. -/
theorem channelHockeyStick_exponential (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (R : ℝ)
    (hR : (regularizedD Φ Ψ).toReal < R) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      channelHockeyStick (Φ.tensorPower k) (Ψ.tensorPower k) ((2 : ℝ) ^ ((k : ℝ) * R)) ≤
        K * Real.exp (-γ * k) := by
  obtain ⟨K, γ, hK, hγ, C, N, hC⟩ := theorem_2_2 Φ Ψ ha
    Φ.stinespring Ψ.stinespring Φ.stinespring_isometry Ψ.stinespring_isometry
    (dilationMap_stinespring Φ) (dilationMap_stinespring Ψ) hfinite R hR
  refine ⟨2 * K, γ, by positivity, hγ, N, ?_⟩
  intro k hk
  have hCk := hC k hk
  have hsqrt : Real.sqrt ((2 : ℝ) ^ ((k : ℝ) * R)) =
      (2 : ℝ) ^ ((k : ℝ) * R / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hmin := auxiliaryMinimum_le (powerDilation Φ.stinespring k)
    (powerDilation Ψ.stinespring k) ((2 : ℝ) ^ ((k : ℝ) * R)) (C k)
    (hCk.1.trans_eq hsqrt.symm)
  have hupper := channelHockeyStick_le_minimum_error (Φ.tensorPower k) (Ψ.tensorPower k)
    (pow_pos ha k) (powerDilation Φ.stinespring k) (powerDilation Ψ.stinespring k)
    (powerDilation_isometry Φ.stinespring Φ.stinespring_isometry k)
    (dilationMap_powerDilation Φ Φ.stinespring (dilationMap_stinespring Φ) k)
    (dilationMap_powerDilation Ψ Ψ.stinespring (dilationMap_stinespring Ψ) k)
    ((2 : ℝ) ^ ((k : ℝ) * R)) (by positivity)
  change _ ≤ ‖powerDilation Φ.stinespring k -
    ((1 : Operator (b ^ k)) ⊗ₖ C k) * powerDilation Ψ.stinespring k‖ at hmin
  nlinarith [hmin.trans hCk.2, sq_nonneg (auxiliaryMinimum
    (powerDilation Φ.stinespring k) (powerDilation Ψ.stinespring k)
    ((2 : ℝ) ^ ((k : ℝ) * R)))]

/-- Corollary 5.1's upper-rate limit, for the actual channel hockey stick. -/
theorem channelHockeyStick_tendsto_zero (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (R : ℝ)
    (hR : (regularizedD Φ Ψ).toReal < R) :
    Tendsto (fun k : ℕ => channelHockeyStick (Φ.tensorPower k) (Ψ.tensorPower k)
      ((2 : ℝ) ^ ((k : ℝ) * R))) atTop (𝓝 0) := by
  obtain ⟨K, γ, hK, hγ, N, hN⟩ := channelHockeyStick_exponential Φ Ψ ha hfinite R hR
  have hlim : Tendsto (fun k : ℕ => K * Real.exp (-γ * k)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      TwoRateScalars.stretched_error_tendsto_zero K hγ (by norm_num : (0 : ℝ) < 1)
  exact squeeze_zero' (Eventually.of_forall (fun k =>
    channelHockeyStick_nonneg (Φ.tensorPower k) (Ψ.tensorPower k) (pow_pos ha k) _))
    (eventually_atTop.mpr ⟨N, hN⟩) hlim

/-- Exponential strong converse in Proposition 3.5: every actual parallel
pure test whose alternative acceptance has rate above the regularized channel
relative entropy has exponentially vanishing null acceptance, uniformly over
both the input vector and the output effect. -/
theorem proposition_3_5_exponential_converse (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (R : ℝ)
    (hR : (regularizedD Φ Ψ).toReal < R) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ ψ : UnitPureInput (a ^ k) (a ^ k), ∀ T : Effect (a ^ k * b ^ k),
        T.probability (pureOutput (Ψ.tensorPower k) ψ) ≤ (2 : ℝ) ^ (-(k : ℝ) * R) →
        T.probability (pureOutput (Φ.tensorPower k) ψ) ≤ K * Real.exp (-γ * k) := by
  let S : ℝ := ((regularizedD Φ Ψ).toReal + R) / 2
  have hdS : (regularizedD Φ Ψ).toReal < S := by dsimp [S]; linarith
  have hSR : S < R := by dsimp [S]; linarith
  obtain ⟨K, γ, hK, hγ, N, hN⟩ := channelHockeyStick_exponential Φ Ψ ha hfinite S hdS
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + K, min ((R - S) * Real.log 2) γ, by positivity,
    lt_min (mul_pos (sub_pos.mpr hSR) hlog) hγ, N, ?_⟩
  intro k hk ψ T hq
  have hscore := pureScore_le_channelHockeyStick (Φ.tensorPower k) (Ψ.tensorPower k)
    (pow_pos ha k) ((2 : ℝ) ^ ((k : ℝ) * S)) ψ T
  have hprod : (2 : ℝ) ^ ((k : ℝ) * S) * (2 : ℝ) ^ (-(k : ℝ) * R) =
      Real.exp (-((R - S) * Real.log 2) * k) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  have hqmul := mul_le_mul_of_nonneg_left hq
    (by positivity : 0 ≤ (2 : ℝ) ^ ((k : ℝ) * S))
  rw [hprod] at hqmul
  have hp : T.probability (pureOutput (Φ.tensorPower k) ψ) ≤
      Real.exp (-((R - S) * Real.log 2) * k) + K * Real.exp (-γ * k) := by
    dsimp [pureScore] at hscore
    linarith [hN k hk]
  exact hp.trans (ScalarBounds.exp_sum_le (Nat.cast_nonneg k) hK.le)

/-- Every feasible fixed-error test eventually has a type-II probability
bounded below at each strict rate above the regularized divergence. Taking
the genuine operational infimum preserves that lower bound. -/
theorem eventually_parallelPureBeta_lower (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (ε : ℝ) (hε : ε < 1) (R : ℝ)
    (hR : (regularizedD Φ Ψ).toReal < R) :
    ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ) * R)) ≤ parallelPureBeta Φ Ψ k ε := by
  obtain ⟨K, γ, hK, hγ, N, hN⟩ :=
    proposition_3_5_exponential_converse Φ Ψ ha hfinite R hR
  have hlim : Tendsto (fun k : ℕ => K * Real.exp (-γ * k)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      TwoRateScalars.stretched_error_tendsto_zero K hγ (by norm_num : (0 : ℝ) < 1)
  have hsmall := hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - ε))
  filter_upwards [eventually_ge_atTop N, hsmall] with k hk hsmallk
  apply le_iInf
  intro t
  apply ENNReal.ofReal_le_ofReal
  by_contra! hlt
  have hp := hN k hk t.val.1 t.val.2 hlt.le
  linarith [t.property]

end QuantumChannelStein.ParallelConverse
