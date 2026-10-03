import GeneralizedChannelStein.GeneralDiamondBounds
import GeneralizedChannelStein.SmoothingAttainment

/-! # Homogeneity and finiteness of the full diamond norm of every matrix map

Arbitrary Choi matrices are decomposed into four actual positive matrices;
Choi reconstruction gives four genuine CP maps. No stabilization or tensor
multiplicativity assertion is assumed in this independent finiteness proof.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace GeneralizedChannelStein.GeneralDiamondFiniteness
open QuantumChannelStein Matrix DiamondNorm TraceNorm TestingSDP SmoothingAttainment
  TraceDefectCompletion GeneralDiamondBounds
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {a b : ℕ}

/-- Complex scalar homogeneity of the actual all-reference diamond supremum. -/
theorem diamondNorm_smul (c : ℂ) (Φ : MatrixMap a b) :
    diamondNorm (c • Φ)=ENNReal.ofReal ‖c‖*diamondNorm Φ := by
  have hamp (r : ℕ) (X : Matrix (Fin r × Fin a) (Fin r × Fin a) ℂ) :
      MatrixMap.amplify (c • Φ) r X=c • MatrixMap.amplify Φ r X := rfl
  simp only [diamondNorm,hamp,TraceNorm.traceNorm_smul,ENNReal.ofReal_mul (norm_nonneg c),
    ENNReal.mul_iSup]

/-- The triangle bound for a difference retains genuinely extended values. -/
theorem diamondNorm_sub_le (Φ Ψ : MatrixMap a b) :
    diamondNorm (Φ-Ψ) ≤ diamondNorm Φ+diamondNorm Ψ := by
  rw [sub_eq_add_neg]
  simpa only [diamondNorm_neg] using diamondNorm_add_le Φ (-Ψ)

/-- Hermitian real part of an arbitrary input-first Choi matrix. -/
def choiReal (C : BipartiteOperator a b) : BipartiteOperator a b :=
  (1/2 : ℝ) • (C+Cᴴ)

theorem choiReal_isHermitian (C : BipartiteOperator a b) : (choiReal C).IsHermitian := by
  change (choiReal C)ᴴ=choiReal C
  simp [choiReal,Matrix.conjTranspose_add,add_comm]

/-- A literal real/imaginary decomposition, with both parts Hermitian. -/
theorem choi_real_imag (C : BipartiteOperator a b) :
    C=choiReal C+Complex.I • choiReal (-Complex.I • C) := by
  ext i j
  simp [choiReal,Matrix.conjTranspose_smul,Complex.real_smul]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The norm shift gives a concrete positive-minus-positive decomposition. -/
theorem hermitian_psd_difference (H : BipartiteOperator a b) (hH : H.IsHermitian) :
    ∃ P Q : BipartiteOperator a b, P.PosSemidef ∧ Q.PosSemidef ∧ H=P-Q := by
  letI : CStarAlgebra (BipartiteOperator a b) := CStarAlgebra.mk
  have h : -H ≤ ‖H‖ • (1:BipartiteOperator a b) := by
    simpa only [norm_neg,Algebra.algebraMap_eq_smul_one] using
      hH.neg.isSelfAdjoint.le_algebraMap_norm_self
  change (‖H‖ • (1:BipartiteOperator a b)-(-H)).PosSemidef at h
  refine ⟨‖H‖ • 1+H,‖H‖ • 1,by simpa only [sub_neg_eq_add] using h,
    Matrix.PosSemidef.one.smul (norm_nonneg H),?_⟩
  abel

/-- Four actual CP maps reconstruct every finite-dimensional complex-linear map. -/
theorem exists_four_cp_decomposition (Φ : MatrixMap a b) :
    ∃ P Q R S : MatrixMap a b,
      MatrixMap.CompletelyPositive P ∧ MatrixMap.CompletelyPositive Q ∧
      MatrixMap.CompletelyPositive R ∧ MatrixMap.CompletelyPositive S ∧
      Φ=P-Q+Complex.I • (R-S) := by
  obtain ⟨P,Q,hP,hQ,hR⟩ := hermitian_psd_difference (choiReal (MatrixMap.choi Φ))
    (choiReal_isHermitian _)
  obtain ⟨R,S,hR',hS,hI⟩ := hermitian_psd_difference (choiReal (-Complex.I • MatrixMap.choi Φ))
    (choiReal_isHermitian _)
  have hcp (C : BipartiteOperator a b) (hC : C.PosSemidef) :
      MatrixMap.CompletelyPositive (fromChoi C) := by
    apply (MatrixMap.completelyPositive_iff_choi_positive _).mpr
    rwa [choi_fromChoi]
  refine ⟨fromChoi P,fromChoi Q,fromChoi R,fromChoi S,hcp P hP,hcp Q hQ,hcp R hR',hcp S hS,?_⟩
  apply MatrixMap.choi_injective
  simp only [MatrixMap.choi_add,MatrixMap.choi_sub,MatrixMap.choi_smul,choi_fromChoi]
  rw [← hR,← hI]
  exact choi_real_imag _

/-- Every finite-dimensional complex-linear map has finite full diamond norm.
No positivity, Hermitian preservation, or positive-dimension assumption is needed. -/
theorem diamondNorm_ne_top (Φ : MatrixMap a b) : diamondNorm Φ≠⊤ := by
  obtain ⟨P,Q,R,S,hP,hQ,hR,hS,hΦ⟩ := exists_four_cp_decomposition Φ
  have hbound : diamondNorm Φ ≤ (diamondNorm P+diamondNorm Q)+(diamondNorm R+diamondNorm S) := by
    rw [hΦ]
    apply (diamondNorm_add_le _ _).trans
    rw [diamondNorm_smul,Complex.norm_I,ENNReal.ofReal_one,one_mul]
    exact add_le_add (diamondNorm_sub_le P Q) (diamondNorm_sub_le R S)
  have hfinite : (diamondNorm P+diamondNorm Q)+(diamondNorm R+diamondNorm S)<⊤ := by
    apply ENNReal.add_lt_top.mpr
    constructor
    · exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr (diamondNorm_cp_ne_top P hP),
        lt_top_iff_ne_top.mpr (diamondNorm_cp_ne_top Q hQ)⟩
    · exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr (diamondNorm_cp_ne_top R hR),
        lt_top_iff_ne_top.mpr (diamondNorm_cp_ne_top S hS)⟩
  exact ne_of_lt (hbound.trans_lt hfinite)

end GeneralizedChannelStein.GeneralDiamondFiniteness
