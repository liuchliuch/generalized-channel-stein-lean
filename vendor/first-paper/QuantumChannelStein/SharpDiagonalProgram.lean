import QuantumChannelStein.SharpDiagonalCalculus

/-! # Exact value of the actual geometric-mean program for diagonal pairs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SharpDiagonal
open Matrix Pseudoinverse SupportedGeometricMean CommutingSharpScalars
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] SandwichedRenyi.matrixCStar
variable {n : ℕ}

theorem diagonalChannel_positive_matrix (X : Operator n) (hX : X.PosSemidef) :
    (SharpDivergence.diagonalChannel n).apply X = diag (fun i => (X i i).re) := by
  rw [SharpDivergence.diagonalChannel_apply]
  congr 1
  funext i
  apply Complex.ext
  · rfl
  · simpa only [Matrix.diag, Complex.ofReal_im] using (Complex.nonneg_iff.mp (hX.diag_nonneg (i := i))).2.symm

theorem diag_support (a b : Fin n → ℝ) (hs : ∀ i, b i = 0 → a i = 0) :
    LinearMap.ker (diag b).mulVecLin ≤ LinearMap.ker (diag a).mulVecLin := by
  intro v hv
  change diag b *ᵥ v = 0 at hv
  change diag a *ᵥ v = 0
  ext i
  have hbi := congrFun hv i
  simp only [diag, Matrix.mulVec_diagonal, Pi.mul_apply, Pi.zero_apply] at hbi ⊢
  by_cases hb : b i = 0
  · simp [hs i hb]
  · have hne : (b i : ℂ) ≠ 0 := by exact_mod_cast hb
    rw [(mul_eq_zero.mp hbi).resolve_left hne, mul_zero]

def diagonalFeasible (α : ℝ) (hα : 1 < α) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hs : ∀ i, b i = 0 → a i = 0) :
    SharpDivergence.Feasible (1 / α) (diag a) (diag b) (diag_positive b hb) where
  matrix := diag (fun i => a i ^ α * b i ^ (1 - α))
  positive := diag_positive _ (fun i => mul_nonneg (Real.rpow_nonneg (ha i) _) (Real.rpow_nonneg (hb i) _))
  supported := diag_support _ b (by
    intro i hi
    simp [hs i hi, Real.zero_rpow (show α ≠ 0 by linarith)])
  dominates := by
    rw [mean_diag _ b _ hb (fun i => mul_nonneg (Real.rpow_nonneg (ha i) _) (Real.rpow_nonneg (hb i) _))]
    have heq : (fun i => scalarMean (1 / α) (b i) (a i ^ α * b i ^ (1 - α))) = a := by
      funext i
      exact scalarMean_candidate α (a i) (b i) hα (ha i) (hb i) (hs i)
    rw [heq]

theorem feasible_diagonal_trace_lower (α : ℝ) (hα : 1 < α) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hs : ∀ i, b i = 0 → a i = 0)
    (X : SharpDivergence.Feasible (1 / α) (diag a) (diag b) (diag_positive b hb)) :
    (∑ i, a i ^ α * b i ^ (1 - α)) ≤ X.matrix.trace.re := by
  let x := fun i => (X.matrix i i).re
  have hx : ∀ i, 0 ≤ x i := fun i => (Complex.nonneg_iff.mp (X.positive.diag_nonneg (i := i))).1
  have hα0 : 0 < α := zero_lt_one.trans hα
  let Y := X.map (show 1 / α ∈ Set.Ioc (0 : ℝ) 1 from
    ⟨one_div_pos.mpr hα0, (div_le_one hα0).mpr hα.le⟩) (SharpDivergence.diagonalChannel n)
  have hd := Y.dominates
  have hAeq : (SharpDivergence.diagonalChannel n).apply (diag a) = diag a := by
    simp [SharpDivergence.diagonalChannel_apply, diag]
  have hBeq : (SharpDivergence.diagonalChannel n).apply (diag b) = diag b := by
    simp [SharpDivergence.diagonalChannel_apply, diag]
  have hXeq : Y.matrix = diag x := diagonalChannel_positive_matrix X.matrix X.positive
  have hm := mean_congr (1 / α)
    ((SharpDivergence.diagonalChannel n).apply_positive (diag_positive b hb))
    (diag_positive b hb) hBeq hXeq
  have hd' : diag a ≤ mean (1 / α) (diag b) (diag_positive b hb) (diag x) := by
    calc
      _ = (SharpDivergence.diagonalChannel n).apply (diag a) := hAeq.symm
      _ ≤ mean (1 / α) ((SharpDivergence.diagonalChannel n).apply (diag b))
          ((SharpDivergence.diagonalChannel n).apply_positive (diag_positive b hb)) Y.matrix := hd
      _ = _ := hm
  rw [mean_diag _ b x hb hx] at hd'
  have hentry (i : Fin n) : a i ≤ scalarMean (1 / α) (b i) (x i) := by
    have hi := (sub_nonneg.mpr hd').posSemidef.diag_nonneg (i := i)
    have hr := (Complex.nonneg_iff.mp hi).1
    simpa only [diag, Matrix.sub_apply, Matrix.diagonal_apply_eq, Complex.sub_re, Complex.ofReal_re, sub_nonneg] using hr
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    candidate_le_of_scalarMean_le α (a i) (b i) (x i) hα (ha i) (hb i) (hx i) (hs i) (hentry i))
  simpa only [x, Matrix.trace, Matrix.diag, Complex.re_sum] using hsum

theorem sharp_quasi_diagonal (α : ℝ) (hα : 1 < α) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hs : ∀ i, b i = 0 → a i = 0) :
    SharpDivergence.quasi (1 / α) (diag a) (diag b) (diag_positive b hb) =
      ENNReal.ofReal (∑ i, a i ^ α * b i ^ (1 - α)) := by
  apply le_antisymm
  · have h := SharpDivergence.quasi_le_trace (diagonalFeasible α hα a b ha hb hs)
    simpa only [diagonalFeasible, diag, Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re] using h
  · apply le_iInf
    intro X
    exact ENNReal.ofReal_le_ofReal (feasible_diagonal_trace_lower α hα a b ha hb hs X)

end QuantumChannelStein.SharpDiagonal
