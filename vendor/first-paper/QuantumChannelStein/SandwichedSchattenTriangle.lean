import QuantumChannelStein.SandwichedTraceHolder
import QuantumChannelStein.SchattenScalar

/-! # Genuine rectangular Schatten `2α` triangle inequality

The norm is defined by the spectral trace of `F Fᴴ`. Its triangle inequality
is derived from positive trace Hölder and an ordinary Hilbert-space triangle
inequality on the vectorized entries of `sqrt(Y) F`. No triangle oracle,
SVD assumption, full-rank assumption, or operator-norm substitution is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
attribute [local instance] matrixCStar
variable {n e : ℕ}

theorem gram_positive (F : Matrix (Fin n) (Fin e) ℂ) : (F * Fᴴ).PosSemidef := by
  simpa only [Matrix.conjTranspose_conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self Fᴴ

def schattenTwoAlpha (α : ℝ) (F : Matrix (Fin n) (Fin e) ℂ) : ℝ :=
  powerTrace α (F * Fᴴ) ^ (1 / (2 * α))

theorem schattenTwoAlpha_nonneg (α : ℝ) (F : Matrix (Fin n) (Fin e) ℂ) :
    0 ≤ schattenTwoAlpha α F := Real.rpow_nonneg (powerTrace_nonneg _ _) _

theorem frobeniusNorm_nonneg (F : Matrix (Fin n) (Fin e) ℂ) : 0 ≤ frobeniusNorm F :=
  Real.sqrt_nonneg _

theorem frobeniusVector_add (F G : Matrix (Fin n) (Fin e) ℂ) :
    frobeniusVector (F + G) = frobeniusVector F + frobeniusVector G := by
  ext p
  rfl

theorem frobeniusNorm_add (F G : Matrix (Fin n) (Fin e) ℂ) :
    frobeniusNorm (F + G) ≤ frobeniusNorm F + frobeniusNorm G := by
  rw [frobeniusNorm_eq_vector_norm, frobeniusVector_add,
    frobeniusNorm_eq_vector_norm, frobeniusNorm_eq_vector_norm]
  exact norm_add_le _ _

theorem frobeniusSq_mul_sqrt (F : Matrix (Fin n) (Fin e) ℂ)
    (Y : Operator n) (hY : Y.PosSemidef) :
    frobeniusSq (CFC.sqrt Y * F) = (F * Fᴴ * Y).trace.re := by
  have hR : (CFC.sqrt Y).PosSemidef := (CFC.sqrt_nonneg Y).posSemidef
  have hR2 : CFC.sqrt Y * CFC.sqrt Y = Y := CFC.sqrt_mul_sqrt_self Y hY.nonneg
  have hm : (CFC.sqrt Y * F) * (Fᴴ * CFC.sqrt Y) =
      CFC.sqrt Y * (F * Fᴴ) * CFC.sqrt Y := by simp only [Matrix.mul_assoc]
  rw [frobeniusSq, Matrix.conjTranspose_mul, hR.isHermitian.eq, hm,
    Matrix.trace_mul_cycle, hR2, Matrix.trace_mul_comm]

/-- Hölder controls each weighted Hilbert norm by two actual spectral traces. -/
theorem weighted_frobenius_le_holder {p q : ℝ} (hpq : p.HolderConjugate q)
    (F : Matrix (Fin n) (Fin e) ℂ) (Y : Operator n) (hY : Y.PosSemidef) :
    frobeniusNorm (CFC.sqrt Y * F) ≤
      schattenTwoAlpha p F * powerTrace q Y ^ (1 / (2 * q)) := by
  have hsq : frobeniusNorm (CFC.sqrt Y * F) ^ 2 ≤
      powerTrace p (F * Fᴴ) ^ (1 / p) * powerTrace q Y ^ (1 / q) := by
    rw [frobeniusNorm_sq]
    change frobeniusSq (CFC.sqrt Y * F) ≤ _
    rw [frobeniusSq_mul_sqrt F Y hY]
    exact matrix_trace_holder hpq _ Y (gram_positive F) hY
  exact SchattenScalar.le_root_product_of_sq_le (frobeniusNorm_nonneg _)
    (powerTrace_nonneg _ _) (powerTrace_nonneg _ _) hpq.pos hpq.symm.pos hsq

theorem trace_dual_power_identity (X : Operator n) (hX : X.PosSemidef)
    (p : ℝ) (hp : 1 < p) : (X * CFC.rpow X (p - 1)).trace.re = powerTrace p X := by
  have h := rpow_add_of_sum_ne_zero X hX 1 (p - 1) (by linarith)
  rw [show (1 : ℝ) + (p - 1) = p by ring,
    show CFC.rpow X 1 = X from CFC.rpow_one X hX.nonneg] at h
  exact congrArg (fun A => A.trace.re) h.symm

theorem powerTrace_dual_weight {p q : ℝ} (hpq : p.HolderConjugate q)
    (X : Operator n) (hX : X.PosSemidef) :
    powerTrace q (CFC.rpow X (p - 1)) = powerTrace p X := by
  have h := CFC.rpow_rpow_of_exponent_nonneg X (p - 1) q hpq.sub_one_pos.le hpq.symm.pos.le hX.nonneg
  have hh : CFC.rpow (CFC.rpow X (p - 1)) q = CFC.rpow X p := by
    simpa only [CFC.rpow_eq_pow, hpq.sub_one_mul_conj] using h
  exact congrArg (fun A => A.trace.re) hh

/-- The actual rectangular Schatten `2α` triangle inequality for `α>1`. -/
theorem schattenTwoAlpha_add (α : ℝ) (hα : 1 < α)
    (F G : Matrix (Fin n) (Fin e) ℂ) :
    schattenTwoAlpha α (F + G) ≤ schattenTwoAlpha α F + schattenTwoAlpha α G := by
  let X : Operator n := (F + G) * (F + G)ᴴ
  let s : ℝ := powerTrace α X
  have hX : X.PosSemidef := gram_positive (F + G)
  have hs : 0 ≤ s := powerTrace_nonneg α X
  have ha0 : 0 < α := by linarith
  by_cases hs0 : s = 0
  · change s ^ (1 / (2 * α)) ≤ _
    rw [hs0, Real.zero_rpow (one_div_ne_zero (mul_ne_zero (by norm_num) ha0.ne'))]
    exact add_nonneg (schattenTwoAlpha_nonneg _ _) (schattenTwoAlpha_nonneg _ _)
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  let q : ℝ := α / (α - 1)
  have hpq : α.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hα).mpr rfl
  let Y := CFC.rpow X (α - 1)
  have hY : Y.PosSemidef := CFC.rpow_nonneg.posSemidef
  have hYq : powerTrace q Y = s := powerTrace_dual_weight hpq X hX
  have hroot : frobeniusNorm (CFC.sqrt Y * (F + G)) = Real.sqrt s := by
    rw [frobeniusNorm, frobeniusSq_mul_sqrt _ Y hY]
    change Real.sqrt (X * CFC.rpow X (α - 1)).trace.re = Real.sqrt s
    rw [trace_dual_power_identity X hX α hα]
  have hF := weighted_frobenius_le_holder hpq F Y hY
  have hG := weighted_frobenius_le_holder hpq G Y hY
  rw [hYq] at hF hG
  have htriangle : frobeniusNorm (CFC.sqrt Y * (F + G)) ≤
      frobeniusNorm (CFC.sqrt Y * F) + frobeniusNorm (CFC.sqrt Y * G) := by
    rw [Matrix.mul_add]
    exact frobeniusNorm_add _ _
  have hprod : Real.sqrt s ≤
      (schattenTwoAlpha α F + schattenTwoAlpha α G) * s ^ (1 / (2 * q)) := by
    rw [← hroot]
    exact htriangle.trans ((add_le_add hF hG).trans_eq (by ring))
  rw [SchattenScalar.sqrt_split_holder hspos hpq] at hprod
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hspos (1 / (2 * q)))).mp hprod

end QuantumChannelStein.SandwichedRenyi
