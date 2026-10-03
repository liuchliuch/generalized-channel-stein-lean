import QuantumChannelStein.ChannelDilationPower
import QuantumChannelStein.HockeyStickApproximation
import QuantumChannelStein.TwoRateAmplification
import QuantumChannelStein.ExponentialAmplification
import QuantumChannelStein.ChannelEntropyFiniteness
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Conditional assembly from genuine channel-testing bounds

These theorems explicitly retain the weak-testing inequality as a premise.
They do not claim Theorem 2.2 or Lemma 4.3 without its entropy/data-processing
proof. All dilation/channel-power identifications and amplification steps
are proved for actual matrices.
-/
noncomputable section
namespace QuantumChannelStein.UniformApproximationFromTesting
open scoped BigOperators Kronecker Matrix.Norms.L2Operator Topology
open Matrix ChannelEntropy TensorPower EnvironmentTensor UniformApproximation
  ChannelDilationPower HockeyStickApproximation TestingPrimal Filter

variable {a b eN eM : ℕ}

/-- An actual testing bound for a concrete channel power yields a single
uniform auxiliary operator in the prescribed tensor environments. -/
theorem approxAt_of_channelHockeyStick_bound (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (k : ℕ) (r δ : ℝ) (hδ : 0 ≤ δ)
    (htest : channelHockeyStick (KrausChannel.tensorPower Φ k) (KrausChannel.tensorPower Ψ k)
      ((2 : ℝ) ^ ((k : ℝ) * r)) ≤ δ ^ 2) :
    ApproxAt VN VM k r δ := by
  let t : ℝ := (2 : ℝ) ^ ((k : ℝ) * r)
  have ht : 0 ≤ t := Real.rpow_nonneg (by norm_num) _
  have hmin := auxiliaryMinimum_sq_le_channelHockeyStick
    (KrausChannel.tensorPower Φ k) (KrausChannel.tensorPower Ψ k) (pow_pos ha k)
    (powerDilation VN k) (powerDilation VM k)
    (dilationMap_powerDilation Φ VN hVN k) (dilationMap_powerDilation Ψ VM hVM k) t ht
  obtain ⟨C, hC, herror⟩ := auxiliaryMinimum_attained (powerDilation VN k) (powerDilation VM k) t
  have hsqrt : Real.sqrt t = (2 : ℝ) ^ ((k : ℝ) * r / 2) := by
    dsimp [t]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  refine ⟨indexedAuxiliary k C, ?_, ?_⟩
  · rw [norm_indexedAuxiliary]
    exact hC.trans_eq hsqrt
  · rw [indexedAuxiliary_error]
    change auxiliaryDistance (powerDilation VN k) (powerDilation VM k) C ≤ δ
    rw [herror]
    exact (sq_le_sq₀ (auxiliaryMinimum_nonneg _ _ _) hδ).mp (hmin.trans htest)

/-- Conditional assembly: a genuine weak testing inequality strictly below
one gives exponential uniform approximation at every higher rate, after
applying the checked two-rate and fixed-block amplification theorems. -/
theorem exponential_of_eventual_testing_bound (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVNiso : VNᴴ * VN = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (Dstar : Matrix (Fin eN) (Fin eM) ℂ) (L r R δ : ℝ)
    (hexact : VN = applyEnvironment VM Dstar) (hDstar : ‖Dstar‖ ≤ (2 : ℝ) ^ (L / 2))
    (hr : 0 ≤ r) (hrR : r < R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (htest : ∀ᶠ k : ℕ in atTop,
      channelHockeyStick (KrausChannel.tensorPower Φ k) (KrausChannel.tensorPower Ψ k)
        ((2 : ℝ) ^ ((k : ℝ) * r)) ≤ δ ^ 2) :
    ExponentialAtRate VN VM R := by
  by_cases hLR : L ≤ R
  · exact exponential_of_exact VN VM Dstar L R hexact hDstar hLR
  have hRL : R < L := lt_of_not_ge hLR
  have hweak : ∀ᶠ k : ℕ in atTop, ApproxAt VN VM k r δ := by
    filter_upwards [htest] with k hk
    exact approxAt_of_channelHockeyStick_bound Φ Ψ ha VN VM hVN hVM k r δ hδ0 hk
  have hS : r < (r + R) / 2 := by linarith only [hrR]
  have hSR : (r + R) / 2 < R := by linarith only [hrR]
  have hstretch := TwoRateAmplification.lemma_4_4 VN VM Dstar L r ((r + R) / 2) δ
    hVNiso hexact hDstar hr (hrR.trans hRL) hS hδ0 hδ1 hweak
  exact ExponentialAmplification.fixed_block_exponential VN VM Dstar ((r + R) / 2) L R
    (norm_isometry_le_one VN hVNiso) hexact hDstar
    (TwoRateAmplification.stretched_vanishing VN VM hstretch) hSR

end QuantumChannelStein.UniformApproximationFromTesting

noncomputable section
namespace QuantumChannelStein.UniformApproximationFromTesting
open scoped BigOperators Kronecker Matrix.Norms.L2Operator Topology
open Matrix ChannelEntropy TensorPower EnvironmentTensor UniformApproximation
  ChannelDilationPower HockeyStickApproximation TestingPrimal Filter

/-- The exact numerical weak-testing bound is eventually below a fixed
square strictly smaller than one whenever r>d≥0. -/
theorem exists_eventual_square_bound (F : ℕ → ℝ) {d r : ℝ}
    (hd : 0 ≤ d) (hdr : d < r)
    (hF : ∀ᶠ k : ℕ in atTop, F k ≤ ((k : ℝ) * d + 1) / ((k : ℝ) * r)) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 ∧ ∀ᶠ k : ℕ in atTop, F k ≤ δ ^ 2 := by
  have hr : 0 < r := lt_of_le_of_lt hd hdr
  have hratio0 : 0 ≤ d / r := div_nonneg hd hr.le
  have hratio1 : d / r < 1 := (div_lt_one hr).mpr hdr
  have hroot1 : Real.sqrt (d / r) < 1 := by
    have hsq := Real.sq_sqrt hratio0
    nlinarith only [hsq, hratio1, Real.sqrt_nonneg (d / r)]
  obtain ⟨δ, hδlow, hδ1⟩ := exists_between hroot1
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans hδlow.le
  have hδsq : d / r < δ ^ 2 := by
    have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg (d / r)) hδ0).mpr hδlow
    rwa [Real.sq_sqrt hratio0] at hsq
  have hlim : Tendsto (fun k : ℕ => d / r + r⁻¹ / (k : ℝ)) atTop (𝓝 (d / r)) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat r⁻¹))
  refine ⟨δ, hδ0, hδ1, ?_⟩
  filter_upwards [hF, hlim.eventually (gt_mem_nhds hδsq), eventually_ge_atTop 1]
    with k hk hkδ hkpos
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.succ_le_iff.mp hkpos))
  have heq : ((k : ℝ) * d + 1) / ((k : ℝ) * r) = d / r + r⁻¹ / (k : ℝ) := by
    field_simp [hk0, hr.ne']
  exact hk.trans (heq.trans_le hkδ.le)

/-- Conditional final assembly: the explicitly stated genuine weak-testing
estimates imply exponential uniform approximation above d. Lemma 4.3 is
retained as a hypothesis here and is not replaced by a rate oracle. -/
theorem exponential_of_weak_testing_estimates {a b eN eM : ℕ}
    (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVNiso : VNᴴ * VN = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (Dstar : Matrix (Fin eN) (Fin eM) ℂ) (L d R : ℝ)
    (hexact : VN = applyEnvironment VM Dstar) (hDstar : ‖Dstar‖ ≤ (2 : ℝ) ^ (L / 2))
    (hd : 0 ≤ d) (hdR : d < R)
    (htest : ∀ r : ℝ, d < r → ∀ᶠ k : ℕ in atTop,
      channelHockeyStick (KrausChannel.tensorPower Φ k) (KrausChannel.tensorPower Ψ k)
        ((2 : ℝ) ^ ((k : ℝ) * r)) ≤ ((k : ℝ) * d + 1) / ((k : ℝ) * r)) :
    ExponentialAtRate VN VM R := by
  let r : ℝ := (d + R) / 2
  have hdr : d < r := by dsimp [r]; linarith only [hdR]
  have hrR : r < R := by dsimp [r]; linarith only [hdR]
  obtain ⟨δ, hδ0, hδ1, hbound⟩ := exists_eventual_square_bound
    (fun k => channelHockeyStick (KrausChannel.tensorPower Φ k) (KrausChannel.tensorPower Ψ k)
      ((2 : ℝ) ^ ((k : ℝ) * r))) hd hdr (htest r hdr)
  exact exponential_of_eventual_testing_bound Φ Ψ ha VN VM hVNiso hVN hVM Dstar L r R δ
    hexact hDstar (hd.trans hdr.le) hrR hδ0 hδ1 hbound

/-- Finite actual regularized divergence supplies an exact finite-rate
comparison on any prescribed environment spaces representing the channels. -/
theorem exists_exact_comparison_of_finite_regularizedD {a b eN eM : ℕ}
    (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (hfinite : regularizedD Φ Ψ < ⊤) :
    ∃ D : Matrix (Fin eN) (Fin eM) ℂ, ∃ L : ℝ,
      VN = applyEnvironment VM D ∧ ‖D‖ ≤ (2 : ℝ) ^ (L / 2) := by
  obtain ⟨c, hc, hcp⟩ := (regularizedD_lt_top_iff_exists_cpLe Φ Ψ ha).mp hfinite
  obtain ⟨D, hD, hDn⟩ := exact_auxiliary_map VN VM hc (by rw [hVN, hVM]; exact hcp)
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hpow : (2 : ℝ) ^ (Real.logb 2 c) = c :=
    Real.rpow_logb (by norm_num) (by norm_num) hcpos
  have hsqrt : Real.sqrt c = (2 : ℝ) ^ (Real.logb 2 c / 2) := by
    calc
      Real.sqrt c = Real.sqrt ((2 : ℝ) ^ (Real.logb 2 c)) := congrArg Real.sqrt hpow.symm
      _ = (2 : ℝ) ^ (Real.logb 2 c / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  exact ⟨D, Real.logb 2 c, hD, hDn.trans_eq hsqrt⟩

/-- Conditional finite-divergence assembly with no assumed auxiliary-map
oracle: the sole missing analytical premise is the explicit quantum weak-
testing inequality. It is deliberately not named the full Theorem 2.2. -/
theorem exponential_of_regularized_weak_testing {a b eN eM : ℕ}
    (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ)
    (hVNiso : VNᴴ * VN = 1)
    (hVN : dilationMap VN = Φ.toLinearMap) (hVM : dilationMap VM = Ψ.toLinearMap)
    (d R : ℝ) (hreg : regularizedD Φ Ψ = (d : EReal)) (hdR : d < R)
    (htest : ∀ r : ℝ, d < r → ∀ᶠ k : ℕ in atTop,
      channelHockeyStick (KrausChannel.tensorPower Φ k) (KrausChannel.tensorPower Ψ k)
        ((2 : ℝ) ^ ((k : ℝ) * r)) ≤ ((k : ℝ) * d + 1) / ((k : ℝ) * r)) :
    ExponentialAtRate VN VM R := by
  have hd : 0 ≤ d := by
    apply EReal.coe_le_coe_iff.mp
    change (0 : EReal) ≤ (d : EReal)
    rw [← hreg]
    exact regularizedD_nonneg Φ Ψ ha
  have hfinite : regularizedD Φ Ψ < ⊤ := by
    rw [hreg]
    exact EReal.coe_lt_top d
  obtain ⟨D, L, hexact, hD⟩ :=
    exists_exact_comparison_of_finite_regularizedD Φ Ψ ha VN VM hVN hVM hfinite
  exact exponential_of_weak_testing_estimates Φ Ψ ha VN VM hVNiso hVN hVM D L d R
    hexact hD hd hdR htest


/-- Extract a literal family in the concrete finite environment powers,
with the squared rate bound and an explicit sufficiently-large threshold.
All coordinate maps preserve the genuine operator norm and error. -/
theorem exponentialAtRate_finite_family {a b eN eM : ℕ}
    (VN : Matrix (Fin b × Fin eN) (Fin a) ℂ)
    (VM : Matrix (Fin b × Fin eM) (Fin a) ℂ) (R : ℝ)
    (h : ExponentialAtRate VN VM R) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧
      ∃ C : (k : ℕ) → Matrix (Fin (eN ^ k)) (Fin (eM ^ k)) ℂ,
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        ‖C k‖ ^ 2 ≤ (2 : ℝ) ^ ((k : ℝ) * R) ∧
        ‖powerDilation VN k - ((1 : Operator (b ^ k)) ⊗ₖ C k) * powerDilation VM k‖ ≤
          K * Real.exp (-γ * k) := by
  classical
  obtain ⟨K, γ, hK, hγ, happrox⟩ := h
  let A : (k : ℕ) → Matrix (Index (Fin eN) k) (Index (Fin eM) k) ℂ := fun k =>
    if hk : ApproxAt VN VM k R (K * Real.exp (-γ * k)) then Classical.choose hk else 0
  have hA : ∀ᶠ k : ℕ in atTop,
      ‖A k‖ ≤ (2 : ℝ) ^ ((k : ℝ) * R / 2) ∧
      auxiliaryError VN VM k (A k) ≤ K * Real.exp (-γ * k) := by
    filter_upwards [happrox] with k hk
    dsimp [A]
    rw [dif_pos hk]
    exact Classical.choose_spec hk
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hA
  refine ⟨K, γ, hK, hγ, fun k => finiteAuxiliary k (A k), N, ?_⟩
  intro k hk
  have hAk := hN k hk
  constructor
  · rw [norm_finiteAuxiliary]
    have hsq := pow_le_pow_left₀ (norm_nonneg (A k)) hAk.1 2
    have heq : ((2 : ℝ) ^ ((k : ℝ) * R / 2)) ^ 2 = (2 : ℝ) ^ ((k : ℝ) * R) := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    exact hsq.trans_eq heq
  · change ‖powerDilation VN k - applyEnvironment (powerDilation VM k) (finiteAuxiliary k (A k))‖ ≤ _
    rw [finiteAuxiliary_error]
    exact hAk.2

end QuantumChannelStein.UniformApproximationFromTesting
