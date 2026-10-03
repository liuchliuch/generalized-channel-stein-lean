import QuantumChannelStein.TensorPower
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Actual permutations of tensor factors
These are concrete finite index permutations, a prerequisite for the
permutation-invariant channel comparison in the Fawzi--Fawzi chain rule.
-/
noncomputable section
namespace QuantumChannelStein.TensorPermutation
open TensorPower Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Permute the finite string of tensor coordinates and transport back to
the project's recursive tensor index type. -/
def factorPermutation (ι : Type*) (k : ℕ) (p : Equiv.Perm (Fin k)) :
    Equiv.Perm (Index ι k) where
  toFun x := (indexEquiv ι k).symm (fun i => indexEquiv ι k x (p.symm i))
  invFun x := (indexEquiv ι k).symm (fun i => indexEquiv ι k x (p i))
  left_inv x := by
    apply (indexEquiv ι k).injective
    funext i
    simp
  right_inv x := by
    apply (indexEquiv ι k).injective
    funext i
    simp

@[simp] theorem factorPermutation_coordinates (ι : Type*) (k : ℕ)
    (p : Equiv.Perm (Fin k)) (x : Index ι k) (i : Fin k) :
    indexEquiv ι k (factorPermutation ι k p x) i = indexEquiv ι k x (p.symm i) := by
  simp [factorPermutation]

@[simp] theorem factorPermutation_symm_coordinates (ι : Type*) (k : ℕ)
    (p : Equiv.Perm (Fin k)) (x : Index ι k) (i : Fin k) :
    indexEquiv ι k ((factorPermutation ι k p).symm x) i = indexEquiv ι k x (p i) := by
  simp [factorPermutation]

@[simp] theorem factorPermutation_one (ι : Type*) (k : ℕ) :
    factorPermutation ι k 1 = 1 := by
  ext x
  apply (indexEquiv ι k).injective
  funext i
  simp

theorem factorPermutation_mul (ι : Type*) (k : ℕ) (p q : Equiv.Perm (Fin k)) :
    factorPermutation ι k (p * q) = factorPermutation ι k p * factorPermutation ι k q := by
  ext x
  apply (indexEquiv ι k).injective
  funext i
  simp only [factorPermutation_coordinates, Equiv.Perm.mul_apply]
  congr 1

/-- The same permutation on the row and column tensor factors leaves a
repeated rectangular tensor operator unchanged. -/
theorem tensorPower_permutation {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ)
    (k : ℕ) (p : Equiv.Perm (Fin k)) :
    Matrix.reindex (factorPermutation ι k p) (factorPermutation κ k p)
      (tensorPower A k) = tensorPower A k := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, tensorPower_apply_eq_prod,
    factorPermutation_symm_coordinates]
  exact Equiv.prod_comp p (fun l => A (indexEquiv ι k i l) (indexEquiv κ k j l))

/-- Simultaneous relabeling is an actual algebra automorphism on the
square tensor matrices. -/
def conjugation (ι : Type*) [Fintype ι] [DecidableEq ι]
    (k : ℕ) (p : Equiv.Perm (Fin k)) :
    Matrix (Index ι k) (Index ι k) ℂ ≃ₐ[ℂ] Matrix (Index ι k) (Index ι k) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (factorPermutation ι k p)

@[simp] theorem conjugation_tensorPower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (k : ℕ) (p : Equiv.Perm (Fin k)) :
    conjugation ι k p (tensorPower A k) = tensorPower A k :=
  tensorPower_permutation A k p

@[simp] theorem conjugation_one (ι : Type*) [Fintype ι] [DecidableEq ι]
    (k : ℕ) (A : Matrix (Index ι k) (Index ι k) ℂ) :
    conjugation ι k 1 A = A := by
  simp [conjugation, factorPermutation_one]

theorem conjugation_mul (ι : Type*) [Fintype ι] [DecidableEq ι]
    (k : ℕ) (p q : Equiv.Perm (Fin k))
    (A : Matrix (Index ι k) (Index ι k) ℂ) :
    conjugation ι k (p * q) A = conjugation ι k p (conjugation ι k q A) := by
  ext i j
  simp [conjugation, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, factorPermutation_mul]
  change A (((factorPermutation ι k p * factorPermutation ι k q)⁻¹) i)
    (((factorPermutation ι k p * factorPermutation ι k q)⁻¹) j) = _
  rw [_root_.mul_inv_rev]
  rfl

/-- The concrete algebra of matrices invariant under tensor-factor permutations. -/
def invariantAlgebra (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) :
    Subalgebra ℂ (Matrix (Index ι k) (Index ι k) ℂ) where
  carrier := {A | ∀ p, conjugation ι k p A = A}
  mul_mem' := by
    intro A B hA hB p
    rw [map_mul, hA p, hB p]
  add_mem' := by
    intro A B hA hB p
    rw [map_add, hA p, hB p]
  algebraMap_mem' := by
    intro r p
    exact (conjugation ι k p).commutes r

@[simp] theorem mem_invariantAlgebra (ι : Type*) [Fintype ι] [DecidableEq ι]
    (k : ℕ) (A : Matrix (Index ι k) (Index ι k) ℂ) :
    A ∈ invariantAlgebra ι k ↔ ∀ p, conjugation ι k p A = A := Iff.rfl

theorem tensorPower_mem_invariantAlgebra {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (k : ℕ) : tensorPower A k ∈ invariantAlgebra ι k := by
  intro p
  exact conjugation_tensorPower A k p

end QuantumChannelStein.TensorPermutation
