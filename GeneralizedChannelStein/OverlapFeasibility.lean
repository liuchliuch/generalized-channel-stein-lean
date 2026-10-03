import GeneralizedChannelStein.PositiveOverlap

/-! The source's c>1 regime is impossible for a feasible contraction branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GeneralizedChannelStein.OverlapFeasibility
open QuantumChannelStein Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

theorem overlap_le_one (X : Operator a) (ha : 0<a) (hX : ‖X‖≤1)
    (c : ℝ) (hc : 0≤c) (hcover : (BranchExtraction.realPart X-c•1).PosSemidef) : c≤1 := by
  letI : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
  letI : CStarAlgebra (Operator a) := CStarAlgebra.mk
  have hmono := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    ((Matrix.PosSemidef.one (n:=Fin a)).smul hc).nonneg (sub_nonneg.mp hcover.nonneg)
  have hn : ‖c•(1:Operator a)‖=c := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,norm_one,mul_one]
  rw [hn] at hmono
  exact hmono.trans ((BranchExtraction.realPart_norm_le X).trans hX)

theorem feasible_overlap_le_one (J V : Matrix (Fin b) (Fin a) ℂ)
    (hJ : Jᴴ*J=1) (ha : 0<a) (hV : ‖V‖≤1) (c : ℝ) (hc : 0≤c)
    (hcover : (BranchExtraction.realPart (Jᴴ*V)-c•1).PosSemidef) : c≤1 := by
  apply overlap_le_one (Jᴴ*V) ha _ c hc hcover
  have hJn := BranchExtraction.norm_isometry_le_one J hJ
  exact (Matrix.l2_opNorm_mul _ _).trans (by rw [Matrix.l2_opNorm_conjTranspose]; nlinarith [norm_nonneg J,norm_nonneg V])

end GeneralizedChannelStein.OverlapFeasibility
