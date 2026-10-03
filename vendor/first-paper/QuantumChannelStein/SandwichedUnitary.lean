import QuantumChannelStein.SharpUnitary

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SandwichedRenyi
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] matrixCStar
variable {n : ℕ}

def conjugation (U : Matrix.unitaryGroup (Fin n) ℂ) : Operator n ≃⋆ₐ[ℂ] Operator n :=
  Unitary.conjStarAlgAut ℂ (Operator n) U

theorem conjugation_rpow (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : Operator n) (hA : A.PosSemidef) (p : ℝ) :
    conjugation U (CFC.rpow A p) = CFC.rpow (conjugation U A) p := by
  have ha : 0 ≤ conjugation U A := by simpa using OrderHomClass.mono (conjugation U) hA.nonneg
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA.nonneg,
    CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real ha]
  exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) (φ := conjugation U)
    (f := fun x : ℝ => x ^ p) (a := A)
    (hf := A.finite_real_spectrum.continuousOn _)
    (hφ := (conjugation U).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional)
    (ha := hA.isHermitian.isSelfAdjoint)
    (hφa := hA.isHermitian.isSelfAdjoint.map (conjugation U))

theorem trace_conjugation (U : Matrix.unitaryGroup (Fin n) ℂ) (A : Operator n) :
    (conjugation U A).trace = A.trace := by
  change (U.val * A * U.valᴴ).trace = A.trace
  rw [Matrix.trace_mul_cycle, show U.valᴴ * U.val = 1 from by
    simpa only [← Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U,
    Matrix.one_mul]

theorem quasi_unitary (α : ℝ) (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A B : Operator n) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    quasi α (U.val * A * U.valᴴ) (U.val * B * U.valᴴ) = quasi α A B := by
  have hs : sandwichedOperator α (conjugation U A) (conjugation U B) =
      conjugation U (sandwichedOperator α A B) := by
    unfold sandwichedOperator
    rw [← conjugation_rpow U B hB]
    simp only [map_mul]
  change (CFC.rpow (sandwichedOperator α (conjugation U A) (conjugation U B)) α).trace.re = _
  rw [hs, ← conjugation_rpow U _ (sandwichedOperator_positive α hA), trace_conjugation]
  rfl

end QuantumChannelStein.SandwichedRenyi
