import GeneralizedChannelStein.LikelihoodThreshold
import QuantumChannelStein.SharpCommuting
import QuantumChannelStein.AdaptiveCircuit

/-! # A genuine matrix test from commuting likelihood coordinates -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.CommutingLikelihood
open QuantumChannelStein QuantumChannelStein.RelativeEntropy Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Spectral trace entropy is invariant under genuine unitary conjugation. -/
theorem traceFormula_unitary (U : Matrix.unitaryGroup (Fin n) ℂ) (ρ σ : State n) :
    traceFormula ((SharpDivergence.unitaryChannel U).onState ρ)
      ((SharpDivergence.unitaryChannel U).onState σ) = traceFormula ρ σ := by
  let f := SandwichedRenyi.conjugation U
  have hmat (τ : State n) : ((SharpDivergence.unitaryChannel U).onState τ).matrix = f τ.matrix := by
    exact SharpDivergence.unitaryChannel_apply U τ.matrix
  have hcfc (τ : State n) :
      spectralLog2 ((SharpDivergence.unitaryChannel U).onState τ) = f (spectralLog2 τ) := by
    rw [spectralLog2_eq_cfc, spectralLog2_eq_cfc, hmat]
    symm
    exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) (φ := f)
      (f := Real.logb 2) (a := τ.matrix)
      (hf := τ.matrix.finite_real_spectrum.continuousOn _)
      (hφ := f.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional)
      (ha := τ.positive.isHermitian.isSelfAdjoint)
      (hφa := τ.positive.isHermitian.isSelfAdjoint.map f)
  simp only [traceFormula, hcfc, hmat]
  change (f ρ.matrix * (f (spectralLog2 ρ) - f (spectralLog2 σ))).trace.re = _
  rw [← map_sub, ← map_mul]
  exact congrArg Complex.re (SandwichedRenyi.trace_conjugation U _)

/-- The trace formula in any diagonal basis is the actual classical likelihood mean. -/
theorem traceFormula_diagonal (ρ σ : State n) (p q : Fin n → ℝ)
    (hρ : ρ.matrix = SharpDiagonal.diag p) (hσ : σ.matrix = SharpDiagonal.diag q)
    (_hp : ∀ i, 0 ≤ p i) (_hq : ∀ i, 0 ≤ q i)
    (hdom : ∀ i, p i ≠ 0 → q i ≠ 0) :
    traceFormula ρ σ = ∑ i, p i * Real.logb 2 (p i/q i) := by
  simp only [traceFormula, spectralLog2_eq_cfc, hρ, hσ,
    SharpDiagonal.cfc_diag, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [SharpDiagonal.diag_mul, SharpDiagonal.diag_mul]
  simp only [SharpDiagonal.diag, Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p i = 0
  · simp [hi]
  · rw [Real.logb_div hi (hdom i hi)]
    ring

/-- A coordinate indicator is an actual binary quantum effect. -/
def diagonalEffect (s : Fin n → Prop) [DecidablePred s] : Effect n where
  matrix := Matrix.diagonal (fun i => if s i then 1 else 0)
  positive := Matrix.PosSemidef.diagonal (by intro i; change (0 : ℂ) ≤ if s i then 1 else 0; split_ifs <;> norm_num)
  complement_positive := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    exact Matrix.PosSemidef.diagonal (by intro i; change (0 : ℂ) ≤ 1 - (if s i then 1 else 0); split_ifs <;> norm_num)

theorem diagonalEffect_probability (s : Fin n → Prop) [DecidablePred s]
    (ρ : State n) (p : Fin n → ℝ) (hρ : ρ.matrix = SharpDiagonal.diag p) :
    (diagonalEffect s).probability ρ = ∑ i, if s i then p i else 0 := by
  simp only [Effect.probability, diagonalEffect, hρ, SharpDiagonal.diag,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- A finite domination bound and an entropy lower bound produce an actual threshold effect. -/
theorem exists_threshold_effect (ρ σ : State n) (E L ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hEL : E < L)
    (hcomm : Commute ρ.matrix σ.matrix)
    (hdom : (((2 : ℝ)^L) • σ.matrix - ρ.matrix).PosSemidef)
    (hE : E ≤ traceFormula ρ σ) :
    ∃ Q : Effect n, 1-ε ≤ Q.probability ρ ∧
      Q.probability σ ≤ (2 : ℝ)^(-((E-(1-ε)*L)/ε)) := by
  classical
  obtain ⟨U, hdρ, hdσ⟩ := Commute.exists_unitary_qcs
    ρ.positive.isHermitian σ.positive.isHermitian hcomm
  let C := SharpDivergence.unitaryChannel U
  let ρu := C.onState ρ
  let σu := C.onState σ
  let p : Fin n → ℝ := fun i => (ρu.matrix i i).re
  let q : Fin n → ℝ := fun i => (σu.matrix i i).re
  have hp : ∀ i, 0 ≤ p i := fun i => (Complex.nonneg_iff.mp (ρu.positive.diag_nonneg (i := i))).1
  have hq : ∀ i, 0 ≤ q i := fun i => (Complex.nonneg_iff.mp (σu.positive.diag_nonneg (i := i))).1
  have hρ : ρu.matrix = SharpDiagonal.diag p :=
    SharpDivergence.isDiag_eq_real_diag _ ρu.positive (by
      change (C.apply ρ.matrix).IsDiag
      rw [SharpDivergence.unitaryChannel_apply]
      exact hdρ)
  have hσ : σu.matrix = SharpDiagonal.diag q :=
    SharpDivergence.isDiag_eq_real_diag _ σu.positive (by
      change (C.apply σ.matrix).IsDiag
      rw [SharpDivergence.unitaryChannel_apply]
      exact hdσ)
  have hs : ∑ i, p i = 1 := by
    have hh := congrArg Complex.re ρu.trace_one
    rw [hρ] at hh
    simpa [SharpDiagonal.diag, Matrix.trace_diagonal] using hh
  have hdu : (((2 : ℝ)^L) • σu.matrix - ρu.matrix).PosSemidef := by
    have hh := C.apply_positive hdom
    change (C.toLinearMap (((2 : ℝ)^L) • σ.matrix - ρ.matrix)).PosSemidef at hh
    rw [map_sub, LinearMap.map_smul_of_tower] at hh
    exact hh
  have hdp (i : Fin n) : p i ≤ (2 : ℝ)^L * q i := by
    have hh := (Complex.nonneg_iff.mp (hdu.diag_nonneg (i := i))).1
    change 0 ≤ (((2 : ℝ)^L) • σu.matrix i i - ρu.matrix i i).re at hh
    simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul] at hh
    exact sub_nonneg.mp hh
  have hsupport (i : Fin n) (hi : p i ≠ 0) : q i ≠ 0 := by
    intro hqi
    have hh := hdp i
    rw [hqi, mul_zero] at hh
    exact hi (le_antisymm hh (hp i))
  have hEu : E ≤ ∑ i, p i * Real.logb 2 (p i/q i) := by
    rw [← traceFormula_diagonal ρu σu p q hρ hσ hp hq hsupport,
      traceFormula_unitary]
    exact hE
  let t := (E-(1-ε)*L)/ε
  let s : Fin n → Prop := fun i => 0 < p i ∧ t ≤ Real.logb 2 (p i/q i)
  let Q := diagonalEffect s
  refine ⟨C.pullbackEffect Q, ?_, ?_⟩
  · rw [KrausChannel.pullbackEffect_probability]
    change 1-ε ≤ Q.probability ρu
    rw [diagonalEffect_probability s ρu p hρ]
    rw [LikelihoodThreshold.supported_tail_mass p _ hp t]
    exact LikelihoodThreshold.tail_mass_lower p _ hp hs E L ε hε hε1 hEL hEu
      (fun i hi => LikelihoodThreshold.logRatio_le _ _ L hi (hq i) (hdp i))
  · rw [KrausChannel.pullbackEffect_probability]
    change Q.probability σu ≤ _
    rw [diagonalEffect_probability s σu q hσ]
    exact LikelihoodThreshold.likelihood_tail_cost p q hp hq hs t

end GeneralizedChannelStein.CommutingLikelihood
