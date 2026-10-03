import QuantumChannelStein.SharpFeasibleTransport
import QuantumChannelStein.GeometricMeanTensor
import QuantumChannelStein.TensorSupport

/-! # Supported sharp-program tensor and coordinate transport -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QuantumChannelStein.SupportedGeometricMean
open Matrix Pseudoinverse
open scoped Kronecker MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
local instance sharpTensorCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
local instance sharpTensorCStar2 : CStarAlgebra (Matrix κ κ ℂ) := CStarAlgebra.mk
local instance sharpTensorCStar3 : CStarAlgebra (Matrix (ι × κ) (ι × κ) ℂ) := CStarAlgebra.mk

omit [DecidableEq ι] [DecidableEq κ] in
theorem reindex_mul (e : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B :=
  (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e A B).symm

theorem mean_reindex (e : ι ≃ κ) (p : ℝ) (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    mean p (Matrix.reindex e e B) (hB.submatrix e.symm) (Matrix.reindex e e A) =
      Matrix.reindex e e (mean p B hB A) := by
  have hS : (inverseSqrt B hB * A * inverseSqrt B hB).PosSemidef := by
    simpa only [(inverseSqrt_isHermitian B hB).eq] using
      hA.mul_mul_conjTranspose_same (inverseSqrt B hB)
  have hr : root (Matrix.reindex e e B) (hB.submatrix e.symm) = Matrix.reindex e e (root B hB) := by
    rw [root_eq_rpow_half, root_eq_rpow_half, SandwichedRenyi.rpow_reindex e B hB]
  have hi : inverseSqrt (Matrix.reindex e e B) (hB.submatrix e.symm) =
      Matrix.reindex e e (inverseSqrt B hB) := by
    rw [inverseSqrt_eq_rpow_neg_half, inverseSqrt_eq_rpow_neg_half, SandwichedRenyi.rpow_reindex e B hB]
  unfold mean
  rw [hr, hi]
  simp only [← reindex_mul e]
  rw [SandwichedRenyi.rpow_reindex e _ hS]
  simp only [← reindex_mul e]

/-- Order of positive tensor factors is preserved without a commutativity assumption. -/
theorem kronecker_mono (A B : Matrix ι ι ℂ) (C D : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hD : D.PosSemidef) (hAB : A ≤ B) (hCD : C ≤ D) :
    A ⊗ₖ C ≤ B ⊗ₖ D := by
  apply sub_nonneg.mp
  have h := (MatrixMap.posSemidef_kronecker (sub_nonneg.mpr hAB).posSemidef hD).add
    (MatrixMap.posSemidef_kronecker hA (sub_nonneg.mpr hCD).posSemidef)
  convert h.nonneg using 1
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.kroneckerMap_apply]
  ring

/-- Support inclusion tensorizes for arbitrary finite positive matrices. -/
theorem kronecker_support (A B : Matrix ι ι ℂ) (C D : Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
    (hsA : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin)
    (hsC : LinearMap.ker D.mulVecLin ≤ LinearMap.ker C.mulVecLin) :
    LinearMap.ker (B ⊗ₖ D).mulVecLin ≤ LinearMap.ker (A ⊗ₖ C).mulVecLin := by
  obtain ⟨c, hc, hcp⟩ := SupportDomination.exists_domination_of_ker_le hA hB hsA
  obtain ⟨d, hd, hdp⟩ := SupportDomination.exists_domination_of_ker_le hC hD hsC
  have h := kronecker_mono A (c • B) C (d • D) hA (hD.smul (zero_le_one.trans hd))
    (sub_nonneg.mp hcp.nonneg) (sub_nonneg.mp hdp.nonneg)
  have hdom : ((c*d) • (B ⊗ₖ D) - A ⊗ₖ C).PosSemidef := by
    convert (sub_nonneg.mpr h).posSemidef using 1
    ext ⟨i,j⟩ ⟨k,l⟩
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Complex.real_smul, Complex.ofReal_mul]
    ring
  exact SupportDomination.ker_le_of_posSemidef_smul_sub
    (MatrixMap.posSemidef_kronecker hA hC) hdom

end QuantumChannelStein.SupportedGeometricMean

namespace QuantumChannelStein.SharpDivergence
open Matrix SupportedGeometricMean
open scoped Kronecker MatrixOrder Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] SandwichedRenyi.matrixCStar

/-- The same literal feasibility conditions on arbitrary finite coordinates. -/
structure CoordinateFeasible {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (A B : Matrix ι ι ℂ) (hB : B.PosSemidef) where
  matrix : Matrix ι ι ℂ
  positive : matrix.PosSemidef
  supported : LinearMap.ker B.mulVecLin ≤ LinearMap.ker matrix.mulVecLin
  dominates : A ≤ mean p B hB matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
local instance sharpCoordinateCStar1 : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
local instance sharpCoordinateCStar2 : CStarAlgebra (Matrix κ κ ℂ) := CStarAlgebra.mk
local instance sharpCoordinateCStar3 : CStarAlgebra (Matrix (ι × κ) (ι × κ) ℂ) := CStarAlgebra.mk

def CoordinateFeasible.reindex {p : ℝ} {A B : Matrix ι ι ℂ} {hB : B.PosSemidef}
    (X : CoordinateFeasible p A B hB) (e : ι ≃ κ) :
    CoordinateFeasible p (Matrix.reindex e e A) (Matrix.reindex e e B) (hB.submatrix e.symm) where
  matrix := Matrix.reindex e e X.matrix
  positive := X.positive.submatrix e.symm
  supported := (reindex_kernel_inclusion_iff e X.matrix B X.positive hB).mpr X.supported
  dominates := by
    rw [mean_reindex e p X.matrix B X.positive hB]
    have h := (sub_nonneg.mpr X.dominates).posSemidef.submatrix e.symm
    exact sub_nonneg.mp h.nonneg

def CoordinateFeasible.tensor {p : ℝ} {A B : Matrix ι ι ℂ} {C D : Matrix κ κ ℂ}
    {hB : B.PosSemidef} {hD : D.PosSemidef}
    (X : CoordinateFeasible p A B hB) (Y : CoordinateFeasible p C D hD)
    (hA : A.PosSemidef) (_hC : C.PosSemidef) :
    CoordinateFeasible p (A ⊗ₖ C) (B ⊗ₖ D) (MatrixMap.posSemidef_kronecker hB hD) where
  matrix := X.matrix ⊗ₖ Y.matrix
  positive := MatrixMap.posSemidef_kronecker X.positive Y.positive
  supported := kronecker_support X.matrix B Y.matrix D X.positive hB Y.positive hD X.supported Y.supported
  dominates := by
    rw [mean_kronecker p X.matrix B Y.matrix D X.positive hB Y.positive hD]
    exact kronecker_mono A _ C _ hA (mean_positive p D hD Y.matrix) X.dominates Y.dominates

def CoordinateFeasible.transform {p : ℝ} (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    {A B : Matrix ι ι ℂ} {hB : B.PosSemidef} (X : CoordinateFeasible p A B hB)
    (F : Matrix κ ι ℂ) :
    CoordinateFeasible p (F * A * Fᴴ) (F * B * Fᴴ) (hB.mul_mul_conjTranspose_same F) where
  matrix := F * X.matrix * Fᴴ
  positive := X.positive.mul_mul_conjTranspose_same F
  supported := by
    simpa [krausSum] using krausSum_support ({()} : Finset Unit) (fun _ => F)
      X.matrix B X.positive hB X.supported
  dominates := by
    have hd := (sub_nonneg.mpr X.dominates).posSemidef.mul_mul_conjTranspose_same F
    have hh : F * A * Fᴴ ≤ F * mean p B hB X.matrix * Fᴴ := by
      apply sub_nonneg.mp
      simpa only [Matrix.mul_sub, Matrix.sub_mul] using hd.nonneg
    exact hh.trans (transformer p hp X.matrix B X.positive hB X.supported F)

def CoordinateFeasible.cast {p : ℝ} {A B C D : Matrix ι ι ℂ} {hB : B.PosSemidef}
    (X : CoordinateFeasible p A B hB) (hD : D.PosSemidef) (hAC : A = C) (hBD : B = D) :
    CoordinateFeasible p C D hD := by
  subst C
  subst D
  exact X

@[simp] theorem CoordinateFeasible.cast_matrix {p : ℝ} {A B C D : Matrix ι ι ℂ} {hB : B.PosSemidef}
    (X : CoordinateFeasible p A B hB) (hD : D.PosSemidef) (hAC : A = C) (hBD : B = D) :
    (X.cast hD hAC hBD).matrix = X.matrix := by
  subst C
  subst D
  rfl

def Feasible.toCoordinate {n : ℕ} {p : ℝ} {A B : Operator n} {hB : B.PosSemidef}
    (X : Feasible p A B hB) : CoordinateFeasible p A B hB :=
  ⟨X.matrix, X.positive, X.supported, X.dominates⟩

def CoordinateFeasible.toFinite {n : ℕ} {p : ℝ} {A B : Operator n} {hB : B.PosSemidef}
    (X : CoordinateFeasible p A B hB) : Feasible p A B hB :=
  ⟨X.matrix, X.positive, X.supported, X.dominates⟩

end QuantumChannelStein.SharpDivergence
