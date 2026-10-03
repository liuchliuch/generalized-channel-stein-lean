import GeneralizedChannelStein.CorrectionPolynomial

/-! Uniform geometric contraction derived from the actual Hermitian overlap. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.PositiveOverlap
open QuantumChannelStein Matrix BranchExtraction
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a : ℕ}

theorem overlap_gram_identity (X : Operator a) (c lam : ℝ) :
    (1-2*lam*c+lam^2)•(1:Operator a) - (1-lam•X)ᴴ*(1-lam•X) =
      (2*lam)•(BranchExtraction.realPart X-c•1)+lam^2•(1-Xᴴ*X) := by
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_smul,
    star_trivial,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,BranchExtraction.realPart,smul_sub,smul_add]
  module

theorem overlap_gram_bound (X : Operator a) (hX : ‖X‖≤1) (c lam : ℝ) (hlam : 0≤lam)
    (hcover : (BranchExtraction.realPart X-c•1).PosSemidef) :
    ((1-2*lam*c+lam^2)•(1:Operator a) - (1-lam•X)ᴴ*(1-lam•X)).PosSemidef := by
  rw [overlap_gram_identity]
  exact (hcover.smul (by positivity : 0≤2*lam)).add
    ((KrausRecovery.defect_positive X hX).smul (sq_nonneg lam))

/-- A spectral operator inequality implies the genuine L2 operator-norm bound. -/
theorem norm_le_sqrt_of_gram (Y : Operator a) (s : ℝ) (hs : 0≤s)
    (hgram : (s•(1:Operator a)-Yᴴ*Y).PosSemidef) : ‖Y‖≤Real.sqrt s := by
  letI : CStarAlgebra (Operator a) := CStarAlgebra.mk
  have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (Matrix.posSemidef_conjTranspose_mul_self Y).nonneg (sub_nonneg.mp hgram.nonneg)
  have hone : ‖(1:Operator a)‖≤1 := by
    exact TraceNorm.unitary_opNorm_le_one (1:Matrix.unitaryGroup (Fin a) ℂ)
  have hsq : ‖Y‖^2≤s := by
    calc
      _ = ‖Yᴴ*Y‖ := by simpa [pow_two] using (CStarRing.norm_star_mul_self (x:=Y)).symm
      _ ≤ ‖s•(1:Operator a)‖ := hnorm
      _ = s*‖(1:Operator a)‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
      _ ≤ s := by nlinarith
  nlinarith [Real.sq_sqrt hs,Real.sqrt_nonneg s,norm_nonneg Y]

/-- Paper's q₀ = sqrt(1−3c²/4), derived rather than postulated. -/
theorem geometric_contraction (X : Operator a) (hX : ‖X‖≤1) (c : ℝ)
    (hc : 0<c) (hc1 : c≤1) (hcover : (BranchExtraction.realPart X-c•1).PosSemidef) :
    ‖1-(c/2)•X‖≤Real.sqrt (1-3*c^2/4) := by
  have he : 1-2*(c/2)*c+(c/2)^2=1-3*c^2/4 := by ring
  have hs : 0≤1-3*c^2/4 := by nlinarith
  exact norm_le_sqrt_of_gram _ _ hs (by simpa only [he] using overlap_gram_bound X hX c (c/2) (by positivity) hcover)

end GeneralizedChannelStein.PositiveOverlap
