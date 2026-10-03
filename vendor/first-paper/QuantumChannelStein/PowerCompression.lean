import QuantumChannelStein.SandwichedRenyiBridge
import Quantum.TraceInequality.JensenOperatorInequality

/-! # Supported power-perspective prerequisites
Actual Hansen compression for positive powers, including singular operators.
This is a prerequisite of the supported geometric-mean transformer inequality.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.PowerCompression
open scoped ComplexOrder
open LownerHeinzTheorem JensenOperatorInequality

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Positive powers are concave under a genuine contraction compression. -/
theorem rpow_compression (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (A X : H →L[ℂ] H) (hA : 0 ≤ A) (hX : ‖X‖ ≤ 1) :
    star X * CFC.rpow A p * X ≤ CFC.rpow (star X * A * X) p := by
  have hf : CondIciAll.{u} (fun x : ℝ => -(x ^ p)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro K _ _ _ _
      exact power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := K) p ⟨hp.1.le, hp.2⟩
    · exact (Real.continuous_rpow_const hp.1.le).neg.continuousOn
    · simp [Real.zero_rpow hp.1.ne']
  have hspec : spectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A).mp hA x hx
  have h := theorem_2_5_2_i_ici_all_imp_iv (ℋ := H) hf
    (A := A) (X := X) hA.isSelfAdjoint hspec hX
  have hcomp : 0 ≤ star X * A * X := star_left_conjugate_nonneg hA X
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA, CFC.rpow_eq_cfc_real hcomp]
  simpa [LownerHeinzCore.cfcR, LownerHeinzTheorem.cfcR,
    cfc_neg, mul_neg, neg_mul] using neg_le_neg h

section Matrices
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance powerCompressionCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk

theorem toEuclideanCLM_rpow (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (p : ℝ) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (CFC.rpow A p) = CFC.rpow ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A) p := by
  have hmap : 0 ≤ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A := by
    simpa using (OrderHomClass.mono (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) hA.nonneg)
  simp only [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA.nonneg,
    CFC.rpow_eq_cfc_real hmap]
  exact StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ)
    (φ := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι))) (f := fun x : ℝ => x ^ p) (a := A)
    (hf := A.finite_real_spectrum.continuousOn _)
    (hφ := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional)
    (ha := hA.isHermitian.isSelfAdjoint)
    (hφa := hA.isHermitian.isSelfAdjoint.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)))

/-- Concrete square-matrix Hansen inequality, with no invertibility assumption. -/
theorem matrix_rpow_compression (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (A X : Matrix ι ι ℂ) (hA : A.PosSemidef) (hX : ‖X‖ ≤ 1) :
    Xᴴ * CFC.rpow A p * X ≤ CFC.rpow (Xᴴ * A * X) p := by
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    letI := hi
    exact le_of_eq (Subsingleton.elim _ _)
  | inr hi =>
    letI := hi
    have hm : 0 ≤ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A := by
      simpa using (OrderHomClass.mono (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) hA.nonneg)
    have hc := rpow_compression p hp ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) X) hm hX
    have hpA : (Xᴴ * A * X).PosSemidef := hA.conjTranspose_mul_mul_same X
    apply (OrderIsoClass.map_le_map_iff (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι))).mp
    rw [toEuclideanCLM_rpow _ hpA]
    simpa only [← Matrix.star_eq_conjTranspose, map_mul, map_star,
      toEuclideanCLM_rpow A hA] using hc
end Matrices

end QuantumChannelStein.PowerCompression
