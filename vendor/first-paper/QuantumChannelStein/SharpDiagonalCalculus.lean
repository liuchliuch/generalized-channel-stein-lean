import QuantumChannelStein.SharpUnitary
import QuantumChannelStein.CommutingSharpScalars
import QuantumChannelStein.SandwichedScaling

/-! # Exact diagonal formulas for the two actual quasi-divergences -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SharpDiagonal
open Matrix Pseudoinverse SupportedGeometricMean SandwichedRenyi
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] matrixCStar
variable {n : ℕ}

def diag (d : Fin n → ℝ) : Operator n := Matrix.diagonal (fun i => (d i : ℂ))

theorem diag_positive (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) : (diag d).PosSemidef := by
  exact Matrix.PosSemidef.diagonal (fun i => by change (0 : ℂ) ≤ (d i : ℂ); exact_mod_cast hd i)

theorem cfc_diag (d : Fin n → ℝ) (f : ℝ → ℝ) :
    cfc f (diag d) = diag (fun i => f (d i)) := by
  simpa [diag] using SpectralDecomposition.cfc_of_unitary_diagonalization
    (1 : Matrix.unitaryGroup (Fin n) ℂ) d f

theorem root_diag (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    root (diag d) (diag_positive d hd) = diag (fun i => Real.sqrt (d i)) := by
  unfold root
  rw [← (diag_positive d hd).isHermitian.cfc_eq, cfc_diag]

theorem inverseSqrt_diag (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    inverseSqrt (diag d) (diag_positive d hd) = diag (fun i => (Real.sqrt (d i))⁻¹) := by
  unfold inverseSqrt
  rw [← (diag_positive d hd).isHermitian.cfc_eq, cfc_diag]

theorem rpow_diag (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (p : ℝ) :
    CFC.rpow (diag d) p = diag (fun i => d i ^ p) := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real (diag_positive d hd).nonneg, cfc_diag]

theorem diag_mul (d e : Fin n → ℝ) : diag d * diag e = diag (fun i => d i * e i) := by
  simp only [diag, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

theorem mean_diag (p : ℝ) (b x : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hx : ∀ i, 0 ≤ x i) :
    mean p (diag b) (diag_positive b hb) (diag x) =
      diag (fun i => CommutingSharpScalars.scalarMean p (b i) (x i)) := by
  have hinner : diag (fun i => (Real.sqrt (b i))⁻¹) * diag x *
      diag (fun i => (Real.sqrt (b i))⁻¹) = diag (fun i => x i / b i) := by
    rw [diag_mul, diag_mul]
    congr 1
    funext i
    calc
      _ = x i * (Real.sqrt (b i) * Real.sqrt (b i))⁻¹ := by rw [_root_.mul_inv_rev]; ring
      _ = _ := by rw [Real.mul_self_sqrt (hb i)]; rfl
  unfold mean
  rw [root_diag b hb, inverseSqrt_diag b hb, hinner,
    rpow_diag _ (fun i => div_nonneg (hx i) (hb i)) p, diag_mul, diag_mul]
  congr 1
  funext i
  unfold CommutingSharpScalars.scalarMean
  calc
    _ = (Real.sqrt (b i) * Real.sqrt (b i)) * (x i / b i) ^ p := by ring
    _ = _ := by rw [Real.mul_self_sqrt (hb i)]

end QuantumChannelStein.SharpDiagonal
