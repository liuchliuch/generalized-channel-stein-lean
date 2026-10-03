import QuantumChannelStein.ParallelBlockTests
import QuantumChannelStein.SupportedStateStein
import QuantumChannelStein.BlockRateScalars

/-!
# Actual block/padding direct assembly for the parallel Stein limit

The generic assembly takes the explicitly stated ordinary supported-state
Stein theorem; FinalSteinTheorems supplies the proved PhyslibStateStein instance. Repeated inputs, output state powers, ignored remainders,
actual effects, and the operational beta comparison are all constructed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace QuantumChannelStein.ParallelSteinAssembly
open Matrix ChannelEntropy RelativeEntropy PerfectDiscrimination ParallelBlockTests
  OperationalTesting ParallelExponent Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
variable {a b : ℕ}

/-- Finite channel divergence supplies actual support for every chosen pure input block. -/
theorem block_output_support (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (hfinite : regularizedD Φ Ψ < ⊤) (k : ℕ) (ψ : UnitPureInput (a ^ k) (a ^ k)) :
    supportIncluded (pureOutput (Φ.tensorPower k) ψ) (pureOutput (Ψ.tensorPower k) ψ) := by
  obtain ⟨c, hc, hcp⟩ := (regularizedD_lt_top_iff_exists_cpLe Φ Ψ ha).mp hfinite
  exact SupportDomination.ker_le_of_posSemidef_smul_sub (pureOutput (Φ.tensorPower k) ψ).positive
    (pureOutput_domination (Φ.tensorPower k) (Ψ.tensorPower k) (c ^ k)
      (Φ.cpLe_tensorPower Ψ (zero_le_one.trans hc) hcp k) ψ)

/-- A strict rate below the true supremum is witnessed by an actual finite
block and actual normalized pure input, with a strictly larger state rate. -/
theorem exists_strict_block_rate (Φ Ψ : KrausChannel a b) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : (R : EReal) < regularizedD Φ Ψ) :
    ∃ k : ℕ, 0 < k ∧ ∃ ψ : UnitPureInput (a ^ k) (a ^ k), ∃ u : ℝ,
      0 ≤ u ∧ (k : ℝ) * R < u ∧
        (u : EReal) < umegaki (pureOutput (Φ.tensorPower k) ψ) (pureOutput (Ψ.tensorPower k) ψ) := by
  obtain ⟨k, hkval⟩ := lt_iSup_iff.mp hR
  obtain ⟨hk, hkval⟩ := lt_iSup_iff.mp hkval
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hblock : (((k : ℝ) * R : ℝ) : EReal) < channelD (Φ.tensorPower k) (Ψ.tensorPower k) := by
    by_contra! hle
    have hm := mul_le_mul_of_nonneg_left hle
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg k : (0 : ℝ) ≤ k)))
    rw [← EReal.coe_mul, inv_mul_cancel_left₀ hkR] at hm
    exact (not_le_of_gt hkval) hm
  obtain ⟨ψ, hψ⟩ := lt_iSup_iff.mp hblock
  obtain ⟨u, hku, huD⟩ := EReal.exists_between_coe_real hψ
  have hku' : (k : ℝ) * R < u := EReal.coe_lt_coe_iff.mp hku
  exact ⟨k, hk, ψ, u, (mul_nonneg (Nat.cast_nonneg k) hR0).trans hku'.le, hku', huD⟩

/-- Supported-state direct testing gives actual repeated-block and padded
parallel tests at every sufficiently large total blocklength. -/
theorem eventually_parallel_test_of_block (hstein : SupportedStateDirect)
    (Φ Ψ : KrausChannel a b) (ha : 0 < a) (k : ℕ) (hk : 0 < k)
    (ψ : UnitPureInput (a ^ k) (a ^ k))
    (hs : supportIncluded (pureOutput (Φ.tensorPower k) ψ) (pureOutput (Ψ.tensorPower k) ψ))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (R u : ℝ) (hR : 0 ≤ R)
    (hu : 0 ≤ u) (hgap : (k : ℝ) * R < u)
    (huD : (u : EReal) < umegaki (pureOutput (Φ.tensorPower k) ψ) (pureOutput (Ψ.tensorPower k) ψ)) :
    ∀ᶠ N : ℕ in atTop, ∃ φ : UnitPureInput (a ^ N) (a ^ N), ∃ U : Effect (a ^ N * b ^ N),
      1 - ε ≤ U.probability (pureOutput (Φ.tensorPower N) φ) ∧
      U.probability (pureOutput (Ψ.tensorPower N) φ) ≤ (2 : ℝ) ^ (-(N : ℝ) * R) := by
  have htests := supportedStateDirect_effects hstein
    (pureOutput (Φ.tensorPower k) ψ) (pureOutput (Ψ.tensorPower k) ψ) hs ε hε hε1 u hu huD
  filter_upwards [(tendsto_nat_div_atTop k hk).eventually htests,
    eventually_block_cost_ge k hk R u hR hgap] with N hT hcost
  obtain ⟨T, hp, hq⟩ := hT
  have hactual := repeated_padded_test Φ Ψ ha k (N / k) (N % k) ψ T
  rw [Nat.div_add_mod N k] at hactual
  obtain ⟨φ, U, hUp, hUq⟩ := hactual
  refine ⟨φ, U, by rw [hUp]; exact hp, ?_⟩
  rw [hUq]
  exact hq.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

/-- No channel direct-rate oracle remains: the block and pure input are
selected from the actual channel supremum, then tested and padded explicitly. -/
theorem eventually_parallel_test_below_rate (hstein : SupportedStateDirect)
    (Φ Ψ : KrausChannel a b) (ha : 0 < a) (hfinite : regularizedD Φ Ψ < ⊤)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : (R : EReal) < regularizedD Φ Ψ) :
    ∀ᶠ N : ℕ in atTop, ∃ φ : UnitPureInput (a ^ N) (a ^ N), ∃ U : Effect (a ^ N * b ^ N),
      1 - ε ≤ U.probability (pureOutput (Φ.tensorPower N) φ) ∧
      U.probability (pureOutput (Ψ.tensorPower N) φ) ≤ (2 : ℝ) ^ (-(N : ℝ) * R) := by
  obtain ⟨k, hk, ψ, u, hu, hgap, huD⟩ := exists_strict_block_rate Φ Ψ R hR0 hR
  exact eventually_parallel_test_of_block hstein Φ Ψ ha k hk ψ
    (block_output_support Φ Ψ ha hfinite k ψ) ε hε hε1 R u hR0 hu hgap huD

theorem eventually_parallelPureBeta_upper_of_state_direct (hstein : SupportedStateDirect)
    (Φ Ψ : KrausChannel a b) (ha : 0 < a) (hfinite : regularizedD Φ Ψ < ⊤)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : (R : EReal) < regularizedD Φ Ψ) :
    ∀ᶠ N : ℕ in atTop, parallelPureBeta Φ Ψ N ε ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(N : ℝ) * R)) := by
  filter_upwards [eventually_parallel_test_below_rate hstein Φ Ψ ha hfinite ε hε hε1 R hR0 hR]
    with N htest
  obtain ⟨ψ, T, hp, hq⟩ := htest
  have hb : parallelPureBeta Φ Ψ N ε ≤ ENNReal.ofReal (T.probability (pureOutput (Ψ.tensorPower N) ψ)) :=
    iInf_le_of_le ⟨(ψ, T), hp⟩ le_rfl
  exact hb.trans (ENNReal.ofReal_le_ofReal hq)

theorem parallelErrorExponent_nonneg (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) : 0 ≤ parallelErrorExponent Φ Ψ ε N := by
  have h := testingExponent_antitone N (parallelPureBeta_le_one Φ Ψ ha N ε hε)
  simpa only [testingExponent_one] using h

theorem eventually_parallelErrorExponent_ge_of_state_direct (hstein : SupportedStateDirect)
    (Φ Ψ : KrausChannel a b) (ha : 0 < a) (hfinite : regularizedD Φ Ψ < ⊤)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : (R : EReal) < regularizedD Φ Ψ) :
    ∀ᶠ N : ℕ in atTop, (R : EReal) ≤ parallelErrorExponent Φ Ψ ε N := by
  filter_upwards [eventually_parallelPureBeta_upper_of_state_direct hstein Φ Ψ ha hfinite ε hε hε1 R hR0 hR,
    eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  have h := testingExponent_antitone N hN
  rw [testingExponent_two_rpow N hNpos R] at h
  exact h

/-- The actual parallel direct liminf, conditional only on the ordinary
supported-state direct Stein theorem, with all block/padding semantics proved. -/
theorem parallel_liminf_ge_of_state_direct (hstein : SupportedStateDirect)
    (Φ Ψ : KrausChannel a b) (ha : 0 < a) (hfinite : regularizedD Φ Ψ < ⊤)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    regularizedD Φ Ψ ≤ liminf (parallelErrorExponent Φ Ψ ε) atTop := by
  have hzero : (0 : EReal) ≤ liminf (parallelErrorExponent Φ Ψ ε) atTop :=
    le_liminf_of_le (by isBoundedDefault)
      (Eventually.of_forall (parallelErrorExponent_nonneg Φ Ψ ha ε hε.le))
  by_contra! hlt
  obtain ⟨R, hlow, hRd⟩ := EReal.exists_between_coe_real hlt
  have hR0 : 0 ≤ R := EReal.coe_nonneg.mp (hzero.trans hlow.le)
  have hupper : (R : EReal) ≤ liminf (parallelErrorExponent Φ Ψ ε) atTop :=
    le_liminf_of_le (by isBoundedDefault)
      (eventually_parallelErrorExponent_ge_of_state_direct hstein Φ Ψ ha hfinite ε hε hε1 R hR0 hRd)
  exact (not_lt_of_ge hupper) hlow

/-- The full finite-divergence limit of Proposition 3.5, transparently
conditional only on the ordinary supported-state direct Stein input. -/
theorem proposition_3_5_finite_limit_of_state_direct (hstein : SupportedStateDirect)
    (Φ Ψ : KrausChannel a b) (ha : 0 < a) (hfinite : regularizedD Φ Ψ < ⊤)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (parallelErrorExponent Φ Ψ ε) atTop (𝓝 (regularizedD Φ Ψ)) :=
  tendsto_of_le_liminf_of_limsup_le
    (parallel_liminf_ge_of_state_direct hstein Φ Ψ ha hfinite ε hε hε1)
    (proposition_3_5_limsup_le Φ Ψ ha hfinite ε hε hε1)

end QuantumChannelStein.ParallelSteinAssembly
