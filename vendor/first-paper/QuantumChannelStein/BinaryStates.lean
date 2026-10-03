import QuantumChannelStein.BinaryMeasurement
import QuantumChannelStein.SpectralDecompositionCFC

/-! # Binary density matrices and their genuine Umegaki divergence -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.BinaryMeasurement
open Matrix RelativeEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

def binaryState (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : State 2 where
  matrix := Matrix.diagonal ![(p : ℂ), ((1 - p : ℝ) : ℂ)]
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i
    · change (0 : ℂ) ≤ (p : ℂ)
      exact RCLike.ofReal_nonneg.mpr hp
    · change (0 : ℂ) ≤ ((1-p : ℝ) : ℂ)
      exact RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr hp1)
  trace_one := by simp [Matrix.trace_diagonal, Fin.sum_univ_two]

theorem channel_onState_matrix {n : ℕ} (T : Effect n) (ρ : State n) :
    ((channel T).onState ρ).matrix =
      (binaryState (T.probability ρ) (T.probability_nonneg ρ) (T.probability_le_one ρ)).matrix := by
  change (channel T).apply ρ.matrix = _
  rw [channel_apply]
  have him : (T.matrix * ρ.matrix).trace.im = 0 :=
    (Complex.nonneg_iff.mp (trace_mul_nonnegative T.positive ρ.positive)).2.symm
  have ht : (T.matrix * ρ.matrix).trace = (T.probability ρ : ℂ) := by
    apply Complex.ext
    · rfl
    · exact him
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, ρ.trace_one, ht,
    binaryState, Complex.ofReal_sub, Complex.ofReal_one]

theorem cfc_diagonal_real (d : Fin 2 → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  simpa using SpectralDecomposition.cfc_of_unitary_diagonalization
    (1 : Matrix.unitaryGroup (Fin 2) ℂ) d f

theorem binary_spectralLog2 (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    spectralLog2 (binaryState p hp hp1) =
      Matrix.diagonal ![(Real.logb 2 p : ℂ), (Real.logb 2 (1 - p) : ℂ)] := by
  rw [spectralLog2_eq_cfc]
  have hm : (binaryState p hp hp1).matrix =
      Matrix.diagonal (fun i => ((![p, 1-p] : Fin 2 → ℝ) i : ℂ)) := by
    ext i
    fin_cases i <;> rfl
  rw [hm]
  rw [cfc_diagonal_real]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem binary_support (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) :
    supportIncluded (binaryState p hp hp1) (binaryState q hq.le hq1.le) := by
  intro x hx
  have hx' : (binaryState q hq.le hq1.le).matrix *ᵥ x = 0 := LinearMap.mem_ker.mp hx
  have hnq : (1 : ℂ) - (q : ℂ) ≠ 0 := by
    exact_mod_cast (sub_pos.mpr hq1).ne'
  have hz : x = 0 := by
    ext i
    have hi := congrFun hx' i
    fin_cases i
    · simpa [binaryState, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Complex.ofReal_ne_zero.mpr hq.ne'] using hi
    · simpa [binaryState, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        hnq] using hi
  rw [hz]
  exact LinearMap.mem_ker.mpr (by simp)


theorem binary_umegaki (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q < 1) :
    umegaki (binaryState p hp hp1) (binaryState q hq.le hq1.le) =
      ((p * (Real.logb 2 p - Real.logb 2 q) +
        (1-p) * (Real.logb 2 (1-p) - Real.logb 2 (1-q)) : ℝ) : EReal) := by
  rw [umegaki_of_supportIncluded _ _ (binary_support p q hp hp1 hq hq1)]
  congr 1
  unfold traceFormula
  rw [binary_spectralLog2, binary_spectralLog2]
  simp [binaryState, Matrix.diagonal_sub, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Fin.sum_univ_two, Complex.mul_re]

end QuantumChannelStein.BinaryMeasurement
