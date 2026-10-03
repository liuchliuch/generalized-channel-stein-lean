import QuantumChannelStein.RenyiSpectralLowerBound
import QuantumChannelStein.BinaryDataProcessing
import QuantumChannelStein.ScalarBounds

/-! # Actual binary-measurement Rényi testing inequalities -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.BinaryRenyiTesting
open Matrix SandwichedRenyi BinaryMeasurement RelativeEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] SandwichedRenyi.matrixCStar
variable {n : ℕ}

/-- Functional-calculus powers of the genuine binary state are diagonal powers. -/
theorem binary_rpow (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (s : ℝ) :
    CFC.rpow (binaryState q hq hq1).matrix s =
      Matrix.diagonal ![Complex.ofReal (q ^ s), Complex.ofReal ((1 - q) ^ s)] := by
  rw [matrix_rpow_eq_cfc _ (binaryState q hq hq1).positive]
  have hm : (binaryState q hq hq1).matrix =
      Matrix.diagonal (fun i => ((![q, 1-q] : Fin 2 → ℝ) i : ℂ)) := by
    ext i
    fin_cases i <;> rfl
  rw [hm, cfc_diagonal_real]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The first binary outcome already lower-bounds the actual quasi-divergence. -/
theorem first_term_le_binary_quasi (α : ℝ) (hα : 1 < α) (p q : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    p ^ α * q ^ (1 - α) ≤
      quasi α (binaryState p hp hp1).matrix (binaryState q hq.le hq1).matrix := by
  let A := sandwichedOperator α (binaryState p hp hp1).matrix (binaryState q hq.le hq1).matrix
  have hA : A.PosSemidef := sandwichedOperator_positive α (binaryState p hp hp1).positive
  have hs := sum_diagonal_rpow_le_trace A hA α hα.le
  have hdiag : (A 0 0).re = q ^ (sandwichExponent α) * p * q ^ (sandwichExponent α) := by
    simp only [A, sandwichedOperator]
    rw [binary_rpow]
    simp [binaryState, Matrix.diagonal_mul_diagonal, Complex.mul_re]
  have hscalar : (q ^ (sandwichExponent α) * p * q ^ (sandwichExponent α)) ^ α =
      p ^ α * q ^ (1 - α) := by
    rw [show q ^ (sandwichExponent α) * p * q ^ (sandwichExponent α) =
      p * (q ^ (sandwichExponent α) * q ^ (sandwichExponent α)) by ring,
      ← Real.rpow_add hq, Real.mul_rpow hp (by positivity), ← Real.rpow_mul hq.le]
    congr 2
    dsimp [sandwichExponent]
    have ha : α ≠ 0 := by linarith
    field_simp
    ring
  have hsingle : (A 0 0).re ^ α ≤ ∑ i, (A i i).re ^ α :=
    Finset.single_le_sum (fun i _ => Real.rpow_nonneg
      (Complex.nonneg_iff.mp (show (0 : ℂ) ≤ A i i from hA.diag_nonneg)).1 α) (Finset.mem_univ (0 : Fin 2))
  rw [hdiag, hscalar] at hsingle
  exact hsingle.trans hs

/-- Finite genuine Rényi divergence excludes q=0 when an effect has p>0. -/
theorem alternative_positive_of_renyi_le (α : ℝ) (hα : 1 < α)
    (ρ σ : State n) (T : Effect n) (D : ℝ)
    (hD : renyi α hα ρ σ ≤ (D : EReal)) (hp : 0 < T.probability ρ) :
    0 < T.probability σ := by
  have hs := (renyi_lt_top_iff α hα ρ σ).mp (hD.trans_lt (EReal.coe_lt_top D))
  obtain ⟨c, hc, hdom⟩ := (supportIncluded_iff_exists_domination ρ σ).mp hs
  have htest := probability_le_of_domination T ρ σ c hdom
  by_contra! hq
  have hq0 : T.probability σ = 0 := le_antisymm hq (T.probability_nonneg σ)
  rw [hq0, mul_zero] at htest
  linarith

/-- Binary measurement, its exact spectral formula, and the first positive
term prove the logarithmic bound used in the adaptive strong converse. -/
theorem logarithmic_test_bound (α : ℝ) (hα : 1 < α) (ρ σ : State n) (T : Effect n)
    (D : ℝ) (hD : renyi α hα ρ σ ≤ (D : EReal))
    (hp : 0 < T.probability ρ) (hq1 : T.probability σ < 1) :
    α / (α - 1) * Real.log (T.probability ρ) - Real.log (T.probability σ) ≤ D * Real.log 2 := by
  let p := T.probability ρ
  let q := T.probability σ
  have hp0 : 0 ≤ p := T.probability_nonneg ρ
  have hp1 : p ≤ 1 := T.probability_le_one ρ
  have hq : 0 < q := alternative_positive_of_renyi_le α hα ρ σ T D hD hp
  have hbin := (renyi_data_processing α hα (channel T) ρ σ).trans hD
  rw [channel_onState, channel_onState,
    renyi_of_supportIncluded _ _ _ _ (binary_support p q hp0 hp1 hq hq1)] at hbin
  have hreal := EReal.coe_le_coe_iff.mp hbin
  have hterm : 0 < p ^ α * q ^ (1 - α) := mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hq _)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hterm
    (first_term_le_binary_quasi α hα p q hp0 hp1 hq hq1.le)
  have hbase := (div_le_div_of_nonneg_right hlog (sub_pos.mpr hα).le).trans hreal
  rw [Real.logb_mul (Real.rpow_pos_of_pos hp α).ne' (Real.rpow_pos_of_pos hq (1-α)).ne',
    Real.logb_rpow_eq_mul_logb_of_pos hp, Real.logb_rpow_eq_mul_logb_of_pos hq] at hbase
  have hmul := mul_le_mul_of_nonneg_right hbase (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  convert hmul using 1
  dsimp [Real.logb, p, q]
  have ha : α - 1 ≠ 0 := (sub_pos.mpr hα).ne'
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp
  ring

end QuantumChannelStein.BinaryRenyiTesting
