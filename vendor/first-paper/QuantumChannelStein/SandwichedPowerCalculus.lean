import QuantumChannelStein.SandwichedRenyi
import QuantumChannelStein.PseudoinverseCalculus

/-! # Singular finite-spectrum power identities for the sandwiched bound -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
attribute [local instance] matrixCStar
variable {n : ℕ}

theorem matrix_rpow_eq_cfc (B : Operator n) (hB : B.PosSemidef) (p : ℝ) :
    CFC.rpow B p = cfc (fun x : ℝ => x ^ p) B := by
  rw [CFC.rpow_eq_pow]
  exact CFC.rpow_eq_cfc_real hB.nonneg

theorem rpow_product_cfc (B : Operator n) (hB : B.PosSemidef) (a b : ℝ) :
    CFC.rpow B a * CFC.rpow B b = cfc (fun x : ℝ => x ^ a * x ^ b) B := by
  rw [matrix_rpow_eq_cfc B hB, matrix_rpow_eq_cfc B hB]
  exact (cfc_mul _ _ B (B.finite_real_spectrum.continuousOn _)
    (B.finite_real_spectrum.continuousOn _)).symm

theorem rpow_triple_product_cfc (B : Operator n) (hB : B.PosSemidef) (a b c : ℝ) :
    CFC.rpow B a * CFC.rpow B b * CFC.rpow B c =
      cfc (fun x : ℝ => x ^ a * x ^ b * x ^ c) B := by
  rw [rpow_product_cfc B hB, matrix_rpow_eq_cfc B hB]
  exact (cfc_mul _ _ B (B.finite_real_spectrum.continuousOn _)
    (B.finite_real_spectrum.continuousOn _)).symm

/-- Unlike the invertible-only general API, this identity explicitly handles
zero eigenvalues when the sum of exponents is nonzero. -/
theorem rpow_add_of_sum_ne_zero (B : Operator n) (hB : B.PosSemidef)
    (a b : ℝ) (hab : a + b ≠ 0) :
    CFC.rpow B (a + b) = CFC.rpow B a * CFC.rpow B b := by
  rw [matrix_rpow_eq_cfc B hB, rpow_product_cfc B hB]
  apply cfc_congr
  intro x hx
  exact Real.rpow_add' (spectrum_nonneg_of_nonneg hB.nonneg hx) hab

/-- Homogeneity of the actual matrix powers for nonnegative scalars,
including the scalar zero. -/
theorem rpow_real_smul (B : Operator n) (hB : B.PosSemidef) (t p : ℝ) (ht : 0 ≤ t) :
    CFC.rpow (t • B) p = (t ^ p : ℝ) • CFC.rpow B p := by
  rw [matrix_rpow_eq_cfc _ (hB.smul ht), matrix_rpow_eq_cfc B hB]
  rw [← cfc_comp_const_mul t (fun x : ℝ => x ^ p) B
    ((B.finite_real_spectrum.image (fun x : ℝ => t * x)).continuousOn _) hB.isHermitian.isSelfAdjoint]
  rw [← cfc_const_mul (t ^ p : ℝ) (fun x : ℝ => x ^ p) B
    (B.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x hx
  exact Real.mul_rpow ht (spectrum_nonneg_of_nonneg hB.nonneg hx)

theorem sandwichExponent_neg {α : ℝ} (hα : 1 < α) : sandwichExponent α < 0 :=
  div_neg_of_neg_of_pos (sub_neg.mpr hα) (mul_pos (by norm_num) (by linarith))

/-- The sandwich of the alternative by its own negative powers. -/
theorem sandwich_self_eq_rpow (α : ℝ) (hα : 1 < α) (B : Operator n) (hB : B.PosSemidef) :
    sandwichedOperator α B B = CFC.rpow B (1 / α) := by
  have ha0 : 0 < α := by linarith
  have hb0 : sandwichExponent α ≠ 0 := (sandwichExponent_neg hα).ne
  have he : sandwichExponent α + 1 + sandwichExponent α = 1 / α := by
    unfold sandwichExponent
    field_simp
    ring
  have h := rpow_triple_product_cfc B hB (sandwichExponent α) 1 (sandwichExponent α)
  rw [show CFC.rpow B 1 = B from CFC.rpow_one B hB.nonneg] at h
  rw [sandwichedOperator, h, matrix_rpow_eq_cfc B hB]
  apply cfc_congr
  intro x hx
  dsimp only
  have hx0 := spectrum_nonneg_of_nonneg hB.nonneg hx
  by_cases hz : x = 0
  · simp only [hz, Real.zero_rpow hb0, zero_mul,
      Real.zero_rpow (one_div_ne_zero ha0.ne')]
  · have hxp : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hz)
    rw [← Real.rpow_add hxp, ← Real.rpow_add hxp, he]

/-- The zero-sum exponent product is the support projection, not the identity. -/
theorem sandwich_powers_eq_supportProjection (α : ℝ) (hα : 1 < α)
    (B : Operator n) (hB : B.PosSemidef) :
    CFC.rpow B (sandwichExponent α) * CFC.rpow B ((α - 1) / α) *
      CFC.rpow B (sandwichExponent α) = Pseudoinverse.supportProjection B hB := by
  have ha0 : 0 < α := by linarith
  have hb0 : sandwichExponent α ≠ 0 := (sandwichExponent_neg hα).ne
  have he : sandwichExponent α + (α - 1) / α + sandwichExponent α = 0 := by
    unfold sandwichExponent
    field_simp
    ring
  rw [rpow_triple_product_cfc B hB, Pseudoinverse.supportProjection, ← hB.isHermitian.cfc_eq]
  apply cfc_congr
  intro x hx
  dsimp only
  have hx0 := spectrum_nonneg_of_nonneg hB.nonneg hx
  by_cases hz : x = 0
  · simp [hz, hb0]
  · have hxp : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hz)
    rw [← Real.rpow_add hxp, ← Real.rpow_add hxp, he, Real.rpow_zero, if_neg hz]

end QuantumChannelStein.SandwichedRenyi
