import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Spectral square roots and support reconstruction

The inverse square root is defined by finite spectral functional calculus,
with value zero on the kernel. No invertibility assumption is used.
-/

noncomputable section
namespace QuantumChannelStein.Pseudoinverse

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive spectral square root. -/
def root (B : Matrix ι ι ℂ) (hB : B.PosSemidef) : Matrix ι ι ℂ :=
  hB.isHermitian.cfc Real.sqrt

/-- The Moore–Penrose inverse square root, zero on the kernel. -/
def inverseSqrt (B : Matrix ι ι ℂ) (hB : B.PosSemidef) : Matrix ι ι ℂ :=
  hB.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹)

/-- The orthogonal projection onto the support. -/
def supportProjection (B : Matrix ι ι ℂ) (hB : B.PosSemidef) : Matrix ι ι ℂ :=
  hB.isHermitian.cfc (fun x => if x = 0 then 0 else 1)

/-- The Moore–Penrose pseudoinverse from its finite spectral formula. -/
def pseudoinverse (B : Matrix ι ι ℂ) (hB : B.PosSemidef) : Matrix ι ι ℂ :=
  hB.isHermitian.cfc (fun x => x⁻¹)

private theorem spectral_mul (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) : hB.cfc f * hB.cfc g = hB.cfc (fun x => f x * g x) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_mul]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij, Function.comp_def]

private theorem spectral_congr (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) (h : ∀ i, f (hB.eigenvalues i) = g (hB.eigenvalues i)) :
    hB.cfc f = hB.cfc g := by
  have hf : (RCLike.ofReal ∘ f ∘ hB.eigenvalues : ι → ℂ) =
      RCLike.ofReal ∘ g ∘ hB.eigenvalues := by
    funext i
    dsimp
    rw [h i]
  unfold Matrix.IsHermitian.cfc
  rw [hf]

private theorem spectral_id (B : Matrix ι ι ℂ) (hB : B.IsHermitian) :
    hB.cfc (fun x => x) = B := by
  exact hB.spectral_theorem.symm

theorem root_isHermitian (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    (root B hB).IsHermitian := by
  unfold root
  rw [← hB.isHermitian.cfc_eq]
  exact IsSelfAdjoint.cfc

theorem inverseSqrt_isHermitian (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    (inverseSqrt B hB).IsHermitian := by
  unfold inverseSqrt
  rw [← hB.isHermitian.cfc_eq]
  exact IsSelfAdjoint.cfc

theorem supportProjection_isHermitian (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    (supportProjection B hB).IsHermitian := by
  unfold supportProjection
  rw [← hB.isHermitian.cfc_eq]
  exact IsSelfAdjoint.cfc

private theorem spectral_posSemidef (B : Matrix ι ι ℂ) (hB : B.IsHermitian)
    (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hB.eigenvalues i)) : (hB.cfc f).PosSemidef := by
  have hd : (Matrix.diagonal (RCLike.ofReal ∘ f ∘ hB.eigenvalues) :
      Matrix ι ι ℂ).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa only [Pi.zero_apply, Function.comp_apply, RCLike.ofReal_nonneg] using hf i
  exact hd.mul_mul_conjTranspose_same (hB.eigenvectorUnitary : Matrix ι ι ℂ)

theorem root_posSemidef (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    (root B hB).PosSemidef :=
  spectral_posSemidef B hB.isHermitian Real.sqrt (fun _ => Real.sqrt_nonneg _)

theorem inverseSqrt_posSemidef (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    (inverseSqrt B hB).PosSemidef :=
  spectral_posSemidef B hB.isHermitian (fun x => (Real.sqrt x)⁻¹)
    (fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem pseudoinverse_posSemidef (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    (pseudoinverse B hB).PosSemidef :=
  spectral_posSemidef B hB.isHermitian (fun x => x⁻¹)
    (fun i => inv_nonneg.mpr (hB.eigenvalues_nonneg i))

/-- The inverse square root is a genuine square root of the pseudoinverse. -/
theorem inverseSqrt_mul_inverseSqrt (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    inverseSqrt B hB * inverseSqrt B hB = pseudoinverse B hB := by
  unfold inverseSqrt pseudoinverse
  rw [spectral_mul]
  apply spectral_congr
  intro i
  rw [← mul_inv, Real.mul_self_sqrt (hB.eigenvalues_nonneg i)]

/-- Positivity of the pseudoinverse square root in Loewner order. -/
theorem inverseSqrt_positive (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    0 ≤ inverseSqrt B hB :=
  (inverseSqrt_posSemidef B hB).nonneg

/-- Identification with the standard positive square root of the pseudoinverse. -/
theorem sqrt_pseudoinverse (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    CFC.sqrt (pseudoinverse B hB) = inverseSqrt B hB :=
  CFC.sqrt_unique (inverseSqrt_mul_inverseSqrt B hB) (inverseSqrt_positive B hB)

theorem root_mul_root (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    root B hB * root B hB = B := by
  unfold root
  rw [spectral_mul]
  calc
    hB.isHermitian.cfc (fun x => Real.sqrt x * Real.sqrt x) =
        hB.isHermitian.cfc (fun x => x) := by
      apply spectral_congr
      intro i
      exact Real.mul_self_sqrt (hB.eigenvalues_nonneg i)
    _ = B := spectral_id B hB.isHermitian

theorem root_mul_inverseSqrt (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    root B hB * inverseSqrt B hB = supportProjection B hB := by
  unfold root inverseSqrt supportProjection
  rw [spectral_mul]
  apply spectral_congr
  intro i
  by_cases hi : hB.isHermitian.eigenvalues i = 0
  · simp [hi]
  · simp [hi, Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hB.eigenvalues_nonneg i) (Ne.symm hi))]

theorem inverseSqrt_mul_root (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    inverseSqrt B hB * root B hB = supportProjection B hB := by
  unfold root inverseSqrt supportProjection
  rw [spectral_mul]
  apply spectral_congr
  intro i
  by_cases hi : hB.isHermitian.eigenvalues i = 0
  · simp [hi]
  · simp [hi, Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (hB.eigenvalues_nonneg i) (Ne.symm hi))]

/-- Kernel inclusion annihilates every zero eigenvector of the reference. -/
theorem mulVec_eigenvector_eq_zero_of_ker_le
    (A B : Matrix ι ι ℂ) (hB : B.PosSemidef)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin)
    (j : ι) (hj : hB.isHermitian.eigenvalues j = 0) :
    A *ᵥ ⇑(hB.isHermitian.eigenvectorBasis j) = 0 := by
  change A.mulVecLin ⇑(hB.isHermitian.eigenvectorBasis j) = 0
  apply LinearMap.mem_ker.mp
  apply hker
  apply LinearMap.mem_ker.mpr
  change B *ᵥ ⇑(hB.isHermitian.eigenvectorBasis j) = 0
  rw [hB.isHermitian.mulVec_eigenvectorBasis, hj, zero_smul]

/-- A supported matrix is unchanged by multiplying by the support projection. -/
theorem mul_supportProjection_of_ker_le
    (A B : Matrix ι ι ℂ) (hB : B.PosSemidef)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    A * supportProjection B hB = A := by
  let U : Matrix ι ι ℂ := hB.isHermitian.eigenvectorUnitary
  have hcol (j : ι) (hj : hB.isHermitian.eigenvalues j = 0) :
      ∀ i, (A * U) i j = 0 := by
    have hv : (A * U) *ᵥ Pi.single j 1 = 0 := by
      rw [← Matrix.mulVec_mulVec]
      change A *ᵥ (hB.isHermitian.eigenvectorUnitary *ᵥ Pi.single j 1) = 0
      rw [hB.isHermitian.eigenvectorUnitary_mulVec]
      exact mulVec_eigenvector_eq_zero_of_ker_le A B hB hker j hj
    intro i
    have hi := congrFun hv i
    simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply,
      Pi.zero_apply] using hi
  have hd : (A * U) * Matrix.diagonal (fun j =>
      ((if hB.isHermitian.eigenvalues j = 0 then 0 else 1 : ℝ) : ℂ)) = A * U := by
    ext i j
    rw [Matrix.mul_diagonal]
    by_cases hj : hB.isHermitian.eigenvalues j = 0
    · simp [hj, hcol j hj i]
    · simp [hj]
  change A * (U * Matrix.diagonal (fun j =>
      ((if hB.isHermitian.eigenvalues j = 0 then 0 else 1 : ℝ) : ℂ)) * star U) = A
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hd, Matrix.mul_assoc]
  have hu : U * star U = 1 := unitary.coe_mul_star_self hB.isHermitian.eigenvectorUnitary
  rw [hu, Matrix.mul_one]

/-- For a Hermitian supported matrix the left support action is also trivial. -/
theorem supportProjection_mul_of_ker_le
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    supportProjection B hB * A = A := by
  have h := congrArg Matrix.conjTranspose (mul_supportProjection_of_ker_le A B hB hker)
  simpa only [Matrix.conjTranspose_mul, hA.isHermitian.eq,
    (supportProjection_isHermitian B hB).eq] using h

/-- Exact reconstruction by the inverse square root on the reference support. -/
theorem reconstruct_of_ker_le
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) :
    root B hB * (inverseSqrt B hB * A * inverseSqrt B hB) * root B hB = A := by
  calc
    root B hB * (inverseSqrt B hB * A * inverseSqrt B hB) * root B hB =
        (root B hB * inverseSqrt B hB) * A * (inverseSqrt B hB * root B hB) := by
      simp only [Matrix.mul_assoc]
    _ = supportProjection B hB * A * supportProjection B hB := by
      rw [root_mul_inverseSqrt, inverseSqrt_mul_root]
    _ = A := by
      rw [supportProjection_mul_of_ker_le A B hA hB hker,
        mul_supportProjection_of_ker_le A B hB hker]

/-- Multiplying by the pseudoinverse is the support projection. -/
theorem mul_pseudoinverse (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    B * pseudoinverse B hB = supportProjection B hB := by
  calc
    B * pseudoinverse B hB =
        hB.isHermitian.cfc (fun x => x) * hB.isHermitian.cfc (fun x => x⁻¹) := by
      rw [spectral_id]
      rfl
    _ = supportProjection B hB := by
      rw [spectral_mul]
      apply spectral_congr
      intro i
      by_cases hi : hB.isHermitian.eigenvalues i = 0 <;> simp [hi]

/-- The pseudoinverse commutes with the reference matrix. -/
theorem pseudoinverse_mul (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    pseudoinverse B hB * B = supportProjection B hB := by
  have h := congrArg Matrix.conjTranspose (mul_pseudoinverse B hB)
  simpa only [Matrix.conjTranspose_mul, hB.isHermitian.eq,
    (pseudoinverse_posSemidef B hB).isHermitian.eq,
    (supportProjection_isHermitian B hB).eq] using h

/-- First Moore–Penrose reconstruction equation. -/
theorem mul_pseudoinverse_mul (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    B * pseudoinverse B hB * B = B := by
  rw [mul_pseudoinverse]
  exact supportProjection_mul_of_ker_le B B hB hB le_rfl

/-- Second Moore–Penrose reconstruction equation. -/
theorem pseudoinverse_mul_mul_pseudoinverse (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    pseudoinverse B hB * B * pseudoinverse B hB = pseudoinverse B hB := by
  rw [pseudoinverse_mul]
  unfold supportProjection pseudoinverse
  rw [spectral_mul]
  apply spectral_congr
  intro i
  by_cases hi : hB.isHermitian.eigenvalues i = 0 <;> simp [hi]

/-- Third Moore–Penrose equation: the range product is Hermitian. -/
theorem mul_pseudoinverse_isHermitian (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    (B * pseudoinverse B hB).IsHermitian := by
  rw [mul_pseudoinverse]
  exact supportProjection_isHermitian B hB

/-- Fourth Moore–Penrose equation: the initial-space product is Hermitian. -/
theorem pseudoinverse_mul_isHermitian (B : Matrix ι ι ℂ) (hB : B.PosSemidef) :
    (pseudoinverse B hB * B).IsHermitian := by
  rw [pseudoinverse_mul]
  exact supportProjection_isHermitian B hB

end QuantumChannelStein.Pseudoinverse
