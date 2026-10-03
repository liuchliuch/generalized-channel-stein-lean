import QuantumChannelStein.PhyslibStateStein
import QuantumChannelStein.ParallelSteinAssembly
import Mathlib.Data.Nat.Find

/-! Actual below-threshold test families with null acceptance tending to one.
The tolerance is diagonalized; the chosen channel input block is fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.BelowThresholdTestFamilies
open Matrix ChannelEntropy RelativeEntropy OperationalTesting PerfectDiscrimination
  ParallelSteinAssembly ParallelBlockTests Filter
open scoped BigOperators ComplexOrder Topology

/-- A countable diagonal choice upgrades eventual tests at every fixed error
into one family whose acceptance tends to one. No asymptotic conclusion is assumed. -/
theorem diagonal_acceptance_family {X : ℕ → Type*} (fallback : ∀ n, X n)
    (p q : (n : ℕ) → X n → ℝ) (b : ℕ → ℝ)
    (hp1 : ∀ n x, p n x ≤ 1)
    (htests : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ᶠ n : ℕ in atTop, ∃ x : X n, 1 - ε ≤ p n x ∧ q n x ≤ b n) :
    ∃ x : ∀ n, X n, Tendsto (fun n => p n (x n)) atTop (𝓝 1) ∧
      ∀ᶠ n : ℕ in atTop, q n (x n) ≤ b n := by
  classical
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
  have hε0 (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε1 (j : ℕ) : ε j < 1 := by
    dsimp [ε]
    apply (div_lt_one (by positivity : (0 : ℝ) < (j : ℝ) + 2)).mpr
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hM (j : ℕ) : ∃ M : ℕ, ∀ n ≥ M,
      ∃ x : X n, 1 - ε j ≤ p n x ∧ q n x ≤ b n :=
    eventually_atTop.mp (htests (ε j) (hε0 j) (hε1 j))
  choose M hM using hM
  let d : ℕ → ℕ := fun n => Nat.findGreatest (fun j => M j ≤ n) n
  have hd : Tendsto d atTop atTop := by
    apply tendsto_atTop.2
    intro j
    filter_upwards [eventually_ge_atTop (max j (M j))] with n hn
    exact Nat.le_findGreatest ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn)
  let x : ∀ n, X n := fun n =>
    if h : M (d n) ≤ n then Classical.choose (hM (d n) n h) else fallback n
  have hx : ∀ᶠ n : ℕ in atTop, 1 - ε (d n) ≤ p n (x n) ∧ q n (x n) ≤ b n := by
    filter_upwards [eventually_ge_atTop (M 0)] with n hn
    have hh : M (d n) ≤ n := Nat.findGreatest_spec (P := fun j => M j ≤ n) (Nat.zero_le n) hn
    dsimp only [x]
    rw [dif_pos hh]
    exact Classical.choose_spec (hM (d n) n hh)
  have he : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  refine ⟨x, ?_, hx.mono fun n hn => hn.2⟩
  have hlo : Tendsto (fun n => 1 - ε (d n)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (he.comp hd)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    (hx.mono fun n hn => hn.1) (Eventually.of_forall fun n => hp1 n (x n))

/-- Ordinary state tests with one common chosen sequence, not one sequence per tolerance. -/
theorem state_test_family {d : ℕ} (ρ σ : State d) (hs : supportIncluded ρ σ)
    (u : ℝ) (hu : 0 ≤ u) (huD : (u : EReal) < umegaki ρ σ) :
    ∃ T : (m : ℕ) → Effect (d ^ m),
      Tendsto (fun m => (T m).probability (statePower ρ m)) atTop (𝓝 1) ∧
      ∀ᶠ m : ℕ in atTop, (T m).probability (statePower σ m) ≤ (2 : ℝ) ^ (-(m : ℝ) * u) := by
  apply diagonal_acceptance_family
    (fun m => (⟨0, Matrix.PosSemidef.zero, by simpa using (Matrix.PosSemidef.one : (1 : Operator (d ^ m)).PosSemidef)⟩ : Effect (d ^ m)))
    (fun m T => T.probability (statePower ρ m))
    (fun m T => T.probability (statePower σ m))
    (fun m => (2 : ℝ) ^ (-(m : ℝ) * u))
    (fun m T => T.probability_le_one _)
  intro ε hε hε1
  exact supportedStateDirect_effects supportedStateDirect ρ σ hs ε hε hε1 u hu huD

set_option backward.isDefEq.respectTransparency true in
/-- The unsupported branch is constructive: repeat a zero-alternative event.
Thus one actual state-test sequence exists at every finite strict rate, including D=+infinity. -/
theorem state_test_family_of_rate {d : ℕ} (ρ σ : State d)
    (u : ℝ) (hu : 0 ≤ u) (huD : (u : EReal) < umegaki ρ σ) :
    ∃ T : (m : ℕ) → Effect (d ^ m),
      Tendsto (fun m => (T m).probability (statePower ρ m)) atTop (𝓝 1) ∧
      ∀ᶠ m : ℕ in atTop, (T m).probability (statePower σ m) ≤ (2 : ℝ) ^ (-(m : ℝ) * u) := by
  by_cases hs : supportIncluded ρ σ
  · exact state_test_family ρ σ hs u hu huD
  · obtain ⟨T, hp, hq⟩ := exists_effect_of_not_supportIncluded ρ σ hs
    refine ⟨fun m => repeatedEffect T m, ?_, ?_⟩
    · have hlim : Tendsto (fun m : ℕ => (1 - T.probability ρ) ^ m) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one
        (sub_nonneg.mpr (T.probability_le_one ρ)) (by linarith : 1 - T.probability ρ < 1)
      have hs : Tendsto (fun m : ℕ => (1 : ℝ) - (1 - T.probability ρ) ^ m) atTop (𝓝 1) := by
        simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
      exact hs.congr' (Eventually.of_forall fun m => (repeatedEffect_probability T ρ m).symm)
    · exact Eventually.of_forall fun m => by
        rw [repeatedEffect_probability, hq]
        simp only [sub_zero, one_pow, sub_self]
        positivity

variable {a b : ℕ}

/-- The raw repeated pure input with one fixed product-input remainder. -/
def repeatedPaddedInput (ha : 0 < a) (k : ℕ)
    (ψ : UnitPureInput (a ^ k) (a ^ k)) (m ell : ℕ) :
    UnitPureInput (a ^ (blocks k m + ell)) (a ^ (blocks k m + ell)) :=
  combineInput (blocks k m) ell (repeatInput k ψ m) (unitProductInput (pow_pos ha ell))

/-- The corresponding effect ignores all remainder outputs. -/
def repeatedPaddedEffect (k m ell : ℕ) (T : Effect ((a ^ k * b ^ k) ^ m)) :
    Effect (a ^ (blocks k m + ell) * b ^ (blocks k m + ell)) :=
  reindexEffect (combineOutput a b (blocks k m) ell)
    (ignoreTail (repeatedTest k m T) (a ^ ell * b ^ ell))

theorem repeatedPadded_probability (Φ : KrausChannel a b) (ha : 0 < a) (k m ell : ℕ)
    (ψ : UnitPureInput (a ^ k) (a ^ k)) (T : Effect ((a ^ k * b ^ k) ^ m)) :
    (repeatedPaddedEffect k m ell T).probability
      (pureOutput (Φ.tensorPower (blocks k m + ell)) (repeatedPaddedInput ha k ψ m ell)) =
      T.probability (statePower (pureOutput (Φ.tensorPower k) ψ) m) := by
  rw [repeatedPaddedEffect, repeatedPaddedInput, pureOutput_combineInput,
    reindexEffect_probability, ignoreTail_probability, repeatedTest_probability]

private def castInput {N M : ℕ} (h : N = M)
    (ψ : UnitPureInput (a ^ N) (a ^ N)) : UnitPureInput (a ^ M) (a ^ M) := h ▸ ψ
private def castEffect {N M : ℕ} (h : N = M)
    (T : Effect (a ^ N * b ^ N)) : Effect (a ^ M * b ^ M) := h ▸ T

private theorem cast_probability (Φ : KrausChannel a b) {N M : ℕ} (h : N = M)
    (ψ : UnitPureInput (a ^ N) (a ^ N)) (T : Effect (a ^ N * b ^ N)) :
    (castEffect h T).probability (pureOutput (Φ.tensorPower M) (castInput h ψ)) =
      T.probability (pureOutput (Φ.tensorPower N) ψ) := by
  subst M
  rfl

private theorem block_length (k N : ℕ) : blocks k (N / k) + N % k = N := by
  simpa only [blocks_eq_mul] using Nat.div_add_mod N k

/-- At every total blocklength, repeat the same chosen block and pad its remainder.
This input family is independent of the tests and of every error tolerance. -/
def fixedBlockInput (ha : 0 < a) (k : ℕ) (ψ : UnitPureInput (a ^ k) (a ^ k))
    (N : ℕ) : UnitPureInput (a ^ N) (a ^ N) :=
  castInput (block_length k N) (repeatedPaddedInput ha k ψ (N / k) (N % k))

def fixedBlockEffect (k N : ℕ) (T : Effect ((a ^ k * b ^ k) ^ (N / k))) :
    Effect (a ^ N * b ^ N) :=
  castEffect (block_length k N) (repeatedPaddedEffect k (N / k) (N % k) T)

/-- Exact Born probabilities for the fixed repeated-block family. -/
theorem fixedBlock_probability (Φ : KrausChannel a b) (ha : 0 < a) (k N : ℕ)
    (ψ : UnitPureInput (a ^ k) (a ^ k)) (T : Effect ((a ^ k * b ^ k) ^ (N / k))) :
    (fixedBlockEffect k N T).probability (pureOutput (Φ.tensorPower N) (fixedBlockInput ha k ψ N)) =
      T.probability (statePower (pureOutput (Φ.tensorPower k) ψ) (N / k)) := by
  rw [fixedBlockEffect, fixedBlockInput, cast_probability, repeatedPadded_probability]

/-- The paper's below-threshold sentence, including its fixed input-block structure,
at every strict nonnegative rate, including infinite channel divergence.
Only the final effects are diagonalized. -/
theorem fixed_block_achievability (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (R : ℝ) (hR0 : 0 ≤ R)
    (hR : (R : EReal) < regularizedD Φ Ψ) :
    ∃ k : ℕ, 0 < k ∧ ∃ ψ : UnitPureInput (a ^ k) (a ^ k),
      ∃ T : (N : ℕ) → Effect (a ^ N * b ^ N),
        Tendsto (fun N => (T N).probability
          (pureOutput (Φ.tensorPower N) (fixedBlockInput ha k ψ N))) atTop (𝓝 1) ∧
        ∀ᶠ N : ℕ in atTop, (T N).probability
          (pureOutput (Ψ.tensorPower N) (fixedBlockInput ha k ψ N)) ≤ (2 : ℝ) ^ (-(N : ℝ) * R) := by
  obtain ⟨k, hk, ψ, u, hu, hgap, huD⟩ := exists_strict_block_rate Φ Ψ R hR0 hR
  obtain ⟨U, hp, hq⟩ := state_test_family_of_rate
    (pureOutput (Φ.tensorPower k) ψ) (pureOutput (Ψ.tensorPower k) ψ) u hu huD
  refine ⟨k, hk, ψ, fun N => fixedBlockEffect k N (U (N / k)), ?_, ?_⟩
  · simp_rw [fixedBlock_probability]
    exact hp.comp (tendsto_nat_div_atTop k hk)
  · filter_upwards [(tendsto_nat_div_atTop k hk).eventually hq,
      eventually_block_cost_ge k hk R u hR0 hgap] with N hN hcost
    rw [fixedBlock_probability]
    exact hN.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

/-- One actual pure fixed-reference test family attains every nonnegative rate
strictly below the regularized channel divergence, with null acceptance tending to one. -/
theorem exists_pure_test_family (Φ Ψ : KrausChannel a b) (ha : 0 < a)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : (R : EReal) < regularizedD Φ Ψ) :
    ∃ ψ : (N : ℕ) → UnitPureInput (a ^ N) (a ^ N),
      ∃ T : (N : ℕ) → Effect (a ^ N * b ^ N),
        Tendsto (fun N => (T N).probability (pureOutput (Φ.tensorPower N) (ψ N))) atTop (𝓝 1) ∧
        ∀ᶠ N : ℕ in atTop, (T N).probability (pureOutput (Ψ.tensorPower N) (ψ N)) ≤
          (2 : ℝ) ^ (-(N : ℝ) * R) := by
  obtain ⟨k, hk, ψ, T, hp, hq⟩ := fixed_block_achievability Φ Ψ ha R hR0 hR
  exact ⟨fixedBlockInput ha k ψ, T, hp, hq⟩

end QuantumChannelStein.BelowThresholdTestFamilies
