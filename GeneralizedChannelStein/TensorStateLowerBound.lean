import QuantumChannelStein.PerfectDiscrimination
import QuantumChannelStein.SharpTensorTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.TensorStateLowerBound
open QuantumChannelStein Matrix TensorPower
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem tensorPower_lower {b : ℕ} (ω : State b) (w : ℝ) (hw : 0 ≤ w)
    (hω : (ω.matrix-w•(1:Operator b)).PosSemidef) (n : ℕ) :
    (tensorPower ω.matrix n - w^n • (1 : Matrix (Index (Fin b) n) (Index (Fin b) n) ℂ)).PosSemidef := by
  induction n with
  | zero =>
    rw [pow_zero,one_smul]
    have heq : tensorPower ω.matrix 0 = (1 : Matrix (Index (Fin b) 0) (Index (Fin b) 0) ℂ) := by
      ext i j
      simp [tensorPower,Matrix.one_apply,Subsingleton.elim i j]
    rw [heq,sub_self]
    exact Matrix.PosSemidef.zero
  | succ n ih =>
    have h := SupportedGeometricMean.kronecker_mono (w•(1:Operator b)) ω.matrix
      (w^n • (1 : Matrix (Index (Fin b) n) (Index (Fin b) n) ℂ)) (tensorPower ω.matrix n)
      (Matrix.PosSemidef.one.smul hw) (PerfectDiscrimination.tensorPower_posSemidef _ ω.positive n)
      (sub_nonneg.mp hω.nonneg) (sub_nonneg.mp ih.nonneg)
    have hx : w^(n+1) • (1 : Matrix (Index (Fin b) (n+1)) (Index (Fin b) (n+1)) ℂ) ≤ tensorPower ω.matrix (n+1) := by
      simpa only [tensorPower_succ,Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,
        Matrix.one_kronecker_one,pow_succ] using h
    exact (sub_nonneg.mpr hx).posSemidef

theorem statePower_lower {b : ℕ} (ω : State b) (w : ℝ) (hw : 0 ≤ w)
    (hω : (ω.matrix-w•(1:Operator b)).PosSemidef) (n : ℕ) :
    ((PerfectDiscrimination.statePower ω n).matrix-w^n•(1:Operator (b^n))).PosSemidef := by
  have h := (tensorPower_lower ω w hw hω n).submatrix (ChannelPowerReindex.channelIndexEquiv b n).symm
  convert h using 1
  ext i j
  simp [PerfectDiscrimination.statePower,Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.one_apply]
end GeneralizedChannelStein.TensorStateLowerBound
