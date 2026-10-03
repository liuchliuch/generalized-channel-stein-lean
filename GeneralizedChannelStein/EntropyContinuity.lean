import QuantumChannelStein.PhyslibStateBridge
import QuantumChannelStein.RelativeEntropyBound
import QuantumChannelStein.RelativeEntropyNonneg
import QuantumChannelStein.TraceNormCoordinates
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! Actual von Neumann entropy in bits and finite-state mixture estimates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.EntropyContinuity
open QuantumChannelStein QuantumChannelStein.RelativeEntropy Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual spectral entropy, in bits. -/
def entropy (ρ : State n) : ℝ := -(ρ.matrix * spectralLog2 ρ).trace.re

theorem entropy_eq_physlib (ρ : State n) :
    entropy ρ = Sᵥₙ (PhyslibStateBridge.toMState ρ) / Real.log 2 := by
  rw [Sᵥₙ_eq_neg_trace_log, HermitianMat.inner_eq_re_trace,
    entropy, PhyslibStateBridge.spectralLog2_eq_scaled_log,
    Matrix.mul_smul, Matrix.trace_smul]
  simp only [Complex.smul_re, smul_eq_mul, div_eq_mul_inv]
  rw [Matrix.trace_mul_comm]
  change -((Real.log 2)⁻¹ * ((PhyslibStateBridge.toMState ρ).M.log.mat * ρ.matrix).trace.re) =
    -((PhyslibStateBridge.toMState ρ).M.log.mat * ρ.matrix).trace.re * (Real.log 2)⁻¹
  ring

theorem entropy_nonneg (ρ : State n) : 0 ≤ entropy ρ := by
  rw [entropy_eq_physlib]
  exact div_nonneg (Sᵥₙ_nonneg _) (Real.log_pos (by norm_num)).le

theorem entropy_le_log_dimension (ρ : State n) : entropy ρ ≤ Real.logb 2 n := by
  rw [entropy_eq_physlib, Real.logb]
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
  simpa using Sᵥₙ_le_log_d (PhyslibStateBridge.toMState ρ)

/-- Mixture retains its matrix, not an abstract entropy interface. -/
def mix (ρ σ : State n) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : State n where
  matrix := p • ρ.matrix + (1-p) • σ.matrix
  positive := (ρ.positive.smul hp).add (σ.positive.smul (sub_nonneg.mpr hp1))
  trace_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ρ.trace_one, σ.trace_one]
    simp only [Complex.real_smul]
    push_cast
    ring

theorem traceFormula_entropy (ρ σ : State n) :
    traceFormula ρ σ = -entropy ρ - (ρ.matrix * spectralLog2 σ).trace.re := by
  simp [traceFormula, entropy, Matrix.mul_sub, Matrix.trace_sub]

theorem mix_entropy_identity (ρ σ : State n) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    entropy (mix ρ σ p hp hp1) - (p * entropy ρ + (1-p) * entropy σ) =
      p * traceFormula ρ (mix ρ σ p hp hp1) +
        (1-p) * traceFormula σ (mix ρ σ p hp hp1) := by
  rw [traceFormula_entropy, traceFormula_entropy]
  simp only [entropy, mix, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  ring

/-- Each component is dominated by the reciprocal of its positive weight. -/
theorem mix_domination_left (ρ σ : State n) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ((p⁻¹ : ℝ) • (mix ρ σ p hp.le hp1).matrix - ρ.matrix).PosSemidef := by
  have heq : (p⁻¹ : ℝ) • (mix ρ σ p hp.le hp1).matrix - ρ.matrix =
      (p⁻¹ * (1-p)) • σ.matrix := by
    simp only [mix, smul_add, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
    module
  rw [heq]
  exact σ.positive.smul (mul_nonneg (inv_nonneg.mpr hp.le) (sub_nonneg.mpr hp1))

theorem mix_domination_right (ρ σ : State n) (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) :
    (((1-p)⁻¹ : ℝ) • (mix ρ σ p hp hp1.le).matrix - σ.matrix).PosSemidef := by
  have heq : ((1-p)⁻¹ : ℝ) • (mix ρ σ p hp hp1.le).matrix - σ.matrix =
      ((1-p)⁻¹ * p) • ρ.matrix := by
    simp only [mix, smul_add, smul_smul, inv_mul_cancel₀ (sub_pos.mpr hp1).ne', one_smul]
    module
  rw [heq]
  exact ρ.positive.smul (mul_nonneg (inv_nonneg.mpr (sub_pos.mpr hp1).le) hp)

theorem entropy_mix_lower (ρ σ : State n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p * entropy ρ + (1-p) * entropy σ ≤ entropy (mix ρ σ p hp.le hp1.le) := by
  have hρ := traceFormula_nonneg ρ (mix ρ σ p hp.le hp1.le)
    (SupportDomination.ker_le_of_posSemidef_smul_sub ρ.positive (mix_domination_left ρ σ p hp hp1.le))
  have hσ := traceFormula_nonneg σ (mix ρ σ p hp.le hp1.le)
    (SupportDomination.ker_le_of_posSemidef_smul_sub σ.positive (mix_domination_right ρ σ p hp.le hp1))
  have hid := mix_entropy_identity ρ σ p hp.le hp1.le
  nlinarith [mul_nonneg hp.le hρ, mul_nonneg (sub_pos.mpr hp1).le hσ]

/-- Binary entropy in bits, with totalized endpoint values. -/
def binaryEntropy (p : ℝ) : ℝ := -p * Real.logb 2 p - (1-p) * Real.logb 2 (1-p)

theorem entropy_mix_upper (ρ σ : State n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    entropy (mix ρ σ p hp.le hp1.le) ≤
      p * entropy ρ + (1-p) * entropy σ + binaryEntropy p := by
  have hρ := traceFormula_le_log2_of_domination ρ (mix ρ σ p hp.le hp1.le) p⁻¹
    ((one_le_inv₀ hp).mpr hp1.le) (mix_domination_left ρ σ p hp hp1.le)
  have hσ := traceFormula_le_log2_of_domination σ (mix ρ σ p hp.le hp1.le) (1-p)⁻¹
    ((one_le_inv₀ (sub_pos.mpr hp1)).mpr (by linarith))
    (mix_domination_right ρ σ p hp.le hp1)
  rw [Real.logb_inv] at hρ hσ
  have hid := mix_entropy_identity ρ σ p hp.le hp1.le
  unfold binaryEntropy
  nlinarith [mul_le_mul_of_nonneg_left hρ hp.le,
    mul_le_mul_of_nonneg_left hσ (sub_pos.mpr hp1).le]

/-- The positive and negative Jordan parts have the exact trace-norm mass. -/
theorem jordan_trace_mass (H : HermitianMat (Fin n) ℂ) (htrace : H.trace = 0) :
    H⁺.trace = TraceNorm.traceNorm H.mat / 2 ∧
      H⁻.trace = TraceNorm.traceNorm H.mat / 2 := by
  have hdiff : H⁺.trace - H⁻.trace = 0 := by
    rw [← HermitianMat.trace_sub, HermitianMat.posPart_add_negPart, htrace]
  have hsum : H⁺.trace + H⁻.trace = TraceNorm.traceNorm H.mat := by
    rw [HermitianMat.posPart_eq_cfc_max, HermitianMat.negPart_eq_cfc_min,
      HermitianMat.trace_cfc_eq, HermitianMat.trace_cfc_eq,
      TraceNorm.traceNorm_eq_matrixTraceNorm,
      Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues H.H, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change max (H.H.eigenvalues i) 0 + max (-H.H.eigenvalues i) 0 = |H.H.eigenvalues i|
    by_cases h : 0 ≤ H.H.eigenvalues i
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith), abs_of_neg (lt_of_not_ge h)]; ring
  constructor <;> linarith

/-- Normalize a positive Hermitian matrix with strictly positive trace. -/
def normalizedState (H : HermitianMat (Fin n) ℂ) (hH : 0 ≤ H) (ht : 0 < H.trace) : State n where
  matrix := H.trace⁻¹ • H.mat
  positive := (HermitianMat.zero_le_iff.mp hH).smul (inv_nonneg.mpr ht.le)
  trace_one := by
    rw [Matrix.trace_smul, ← H.trace_eq_trace_rc]
    simp only [Complex.real_smul]
    change ((H.trace⁻¹ : ℝ) : ℂ) * (H.trace : ℂ) = 1
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne']
    rfl

/-- A common mixture controls the entropy difference; all four inputs are
actual states. This is the mixture step used by Jordan decomposition. -/
theorem entropy_sub_le_of_common_mix (ρ σ τ υ : State n) (t : ℝ) (ht : 0 < t)
    (hcommon : ρ.matrix + t • τ.matrix = σ.matrix + t • υ.matrix) :
    entropy ρ - entropy σ ≤ t * Real.logb 2 n +
      (1+t) * binaryEntropy ((1+t)⁻¹) := by
  have hp : 0 < (1+t)⁻¹ := inv_pos.mpr (by linarith)
  have hp1 : (1+t)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr (by linarith)
  have heq : mix ρ τ ((1+t)⁻¹) hp.le hp1.le = mix σ υ ((1+t)⁻¹) hp.le hp1.le := by
    apply (show ∀ (x y : State n), x.matrix = y.matrix → x = y from
      fun ⟨_,_,_⟩ ⟨_,_,_⟩ h => by cases h; rfl)
    change (1+t)⁻¹ • ρ.matrix + (1-(1+t)⁻¹) • τ.matrix =
      (1+t)⁻¹ • σ.matrix + (1-(1+t)⁻¹) • υ.matrix
    have hcoeff : 1-(1+t)⁻¹ = (1+t)⁻¹*t := by field_simp; ring
    rw [hcoeff, SemigroupAction.mul_smul, SemigroupAction.mul_smul, ← smul_add, ← smul_add, hcommon]
  have hlo := entropy_mix_lower ρ τ ((1+t)⁻¹) hp hp1
  have hhi := entropy_mix_upper σ υ ((1+t)⁻¹) hp hp1
  rw [heq] at hlo
  have hτ := entropy_nonneg τ
  have hυ := entropy_le_log_dimension υ
  have hcoeff0 : 0 ≤ 1-(1+t)⁻¹ := by linarith
  have hbound : (1+t)⁻¹ * (entropy ρ-entropy σ) ≤
      (1-(1+t)⁻¹) * Real.logb 2 n + binaryEntropy ((1+t)⁻¹) := by
    nlinarith [mul_nonneg hcoeff0 hτ, mul_le_mul_of_nonneg_left hυ hcoeff0]
  have hmul := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 1+t by linarith)
  have hinv : (1+t)*(1+t)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  simpa only [mul_add, ← mul_assoc, hinv, one_mul, mul_sub, mul_one, add_sub_cancel_left] using hmul

/-- Uniform continuity for arbitrary (also noncommuting or singular) states.
The binary correction is the Jordan-mixture version, not sharp Fannes. -/
theorem entropy_sub_le_trace_distance (ρ σ : State n) :
    let t := TraceNorm.traceNorm (ρ.matrix - σ.matrix) / 2
    entropy ρ - entropy σ ≤ t * Real.logb 2 n +
      (1+t) * binaryEntropy ((1+t)⁻¹) := by
  dsimp only
  let H : HermitianMat (Fin n) ℂ := ⟨ρ.matrix - σ.matrix,
    ρ.positive.isHermitian.sub σ.positive.isHermitian⟩
  let t := TraceNorm.traceNorm H.mat / 2
  have ht0 : 0 ≤ t := div_nonneg (TraceNorm.traceNorm_nonneg _) (by norm_num)
  have htr : H.trace = 0 := by
    rw [HermitianMat.trace_eq_re_trace]
    change (ρ.matrix - σ.matrix).trace.re = 0
    rw [Matrix.trace_sub, ρ.trace_one, σ.trace_one, sub_self]; rfl
  obtain ⟨hplus, hminus⟩ := jordan_trace_mass H htr
  change H⁺.trace = t at hplus
  change H⁻.trace = t at hminus
  by_cases ht : t = 0
  · have hz : ρ.matrix = σ.matrix := by
      have hn : TraceNorm.traceNorm H.mat = 0 := by dsimp [t] at ht; linarith
      rw [TraceNorm.traceNorm_eq_matrixTraceNorm, Matrix.traceNorm_zero_iff] at hn
      exact sub_eq_zero.mp hn
    have hs : ρ = σ := by cases ρ; cases σ; cases hz; rfl
    subst σ
    simp [TraceNorm.traceNorm, binaryEntropy]
  · have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let τ := normalizedState H⁻ H.negPart_nonneg (by rw [hminus]; exact ht)
    let υ := normalizedState H⁺ H.posPart_nonneg (by rw [hplus]; exact ht)
    have hτ : t • τ.matrix = H⁻.mat := by
      change t • (H⁻.trace⁻¹ • H⁻.mat) = _
      rw [hminus, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hυ : t • υ.matrix = H⁺.mat := by
      change t • (H⁺.trace⁻¹ • H⁺.mat) = _
      rw [hplus, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hj := congrArg HermitianMat.mat H.posPart_add_negPart
    change H⁺.mat - H⁻.mat = ρ.matrix - σ.matrix at hj
    have hcommon : ρ.matrix + t • τ.matrix = σ.matrix + t • υ.matrix := by
      rw [hτ, hυ]
      simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp hj).symm
    exact entropy_sub_le_of_common_mix ρ σ τ υ t ht hcommon

/-- Two-sided dimension-dependent continuity in the genuine trace norm. -/
theorem abs_entropy_sub_le_trace_distance (ρ σ : State n) :
    let t := TraceNorm.traceNorm (ρ.matrix - σ.matrix) / 2
    |entropy ρ - entropy σ| ≤ t * Real.logb 2 n +
      (1+t) * binaryEntropy ((1+t)⁻¹) := by
  apply abs_le.mpr
  have h₁ := entropy_sub_le_trace_distance ρ σ
  have h₂ := entropy_sub_le_trace_distance σ ρ
  dsimp only at h₁ h₂ ⊢
  have heq : TraceNorm.traceNorm (σ.matrix - ρ.matrix) =
      TraceNorm.traceNorm (ρ.matrix - σ.matrix) := by
    rw [← neg_sub ρ.matrix σ.matrix, TraceNorm.traceNorm_neg]
  rw [heq] at h₂
  constructor <;> linarith

theorem binaryEntropy_eq (p : ℝ) : binaryEntropy p = Real.binEntropy p / Real.log 2 := by
  simp only [binaryEntropy, Real.binEntropy, Real.log_inv, Real.logb]
  ring

theorem binaryEntropy_le_one (p : ℝ) : binaryEntropy p ≤ 1 := by
  rw [binaryEntropy_eq, div_le_iff₀ (Real.log_pos (by norm_num)), one_mul]
  exact Real.binEntropy_le_log_two

theorem trace_distance_le_one (ρ σ : State n) :
    TraceNorm.traceNorm (ρ.matrix - σ.matrix) / 2 ≤ 1 := by
  have h := TraceNorm.traceNorm_add_le ρ.matrix (-σ.matrix)
  rw [TraceNorm.traceNorm_neg,
    TraceNorm.traceNorm_of_posSemidef _ ρ.positive,
    TraceNorm.traceNorm_of_posSemidef _ σ.positive, ρ.trace_one, σ.trace_one] at h
  change TraceNorm.traceNorm (ρ.matrix - σ.matrix) ≤ 1+1 at h
  linarith

/-- An elementary uniform estimate with a constant correction, useful after
normalizing by block length. No continuity assumption is present. -/
theorem abs_entropy_sub_le_trace_distance_add_two (ρ σ : State n) :
    |entropy ρ - entropy σ| ≤
      TraceNorm.traceNorm (ρ.matrix - σ.matrix) / 2 * Real.logb 2 n + 2 := by
  have h := abs_entropy_sub_le_trace_distance ρ σ
  dsimp only at h
  have ht := trace_distance_le_one ρ σ
  have ht0 := TraceNorm.traceNorm_nonneg (ρ.matrix - σ.matrix)
  have hb := mul_le_mul_of_nonneg_left
    (binaryEntropy_le_one ((1 + TraceNorm.traceNorm (ρ.matrix - σ.matrix) / 2)⁻¹))
    (show 0 ≤ 1 + TraceNorm.traceNorm (ρ.matrix - σ.matrix) / 2 by positivity)
  nlinarith

/-- Uniform over all states at a prescribed trace-distance tolerance. -/
theorem abs_entropy_sub_le_of_traceNorm_le (ρ σ : State n) (δ : ℝ)
    (hδ : TraceNorm.traceNorm (ρ.matrix - σ.matrix) ≤ δ) :
    |entropy ρ - entropy σ| ≤ δ / 2 * Real.logb 2 n + 2 := by
  have hlog : 0 ≤ Real.logb 2 n := (entropy_nonneg ρ).trans (entropy_le_log_dimension ρ)
  exact (abs_entropy_sub_le_trace_distance_add_two ρ σ).trans
    (add_le_add (mul_le_mul_of_nonneg_right (by linarith :
      TraceNorm.traceNorm (ρ.matrix - σ.matrix) / 2 ≤ δ / 2) hlog) le_rfl)

/-- Continuity of the binary correction at zero, including singular states'
zero-distance endpoint. -/
theorem binary_correction_tendsto_zero :
    Filter.Tendsto (fun t : ℝ => (1+t) * binaryEntropy ((1+t)⁻¹))
      (nhds 0) (nhds 0) := by
  have hc : ContinuousAt (fun t : ℝ => (1+t) * binaryEntropy ((1+t)⁻¹)) 0 := by
    simp_rw [binaryEntropy_eq]
    apply ContinuousAt.mul (by fun_prop)
    apply ContinuousAt.div_const
    exact Real.binEntropy_continuous.continuousAt.comp
      ((continuousAt_const.add continuousAt_id).inv₀ (by norm_num))
  simpa [binaryEntropy] using hc.tendsto

end GeneralizedChannelStein.EntropyContinuity
